//! Exact numeric literal syntax, separate from bounded IR indices.
//!
//! Captured GMP limbs are read through the enclosing observation budget.
//! This does not admit a declaration, execute the value, or prove its semantics.
use super::*;

// Stay within the compact object's u16 size field, and bound allocation even
// when the caller supplies a much larger object-access budget.
pub(super) const MAX_LITERAL_LIMBS: usize = 4096;

impl View<'_> {
    pub(super) fn literal_nat(&self, pointer: u64) -> R<Value> {
        if pointer & 1 == 1 {
            return Ok(json!(pointer >> 1));
        }
        if !is_ptr(pointer) {
            return Err("null Nat literal pointer".into());
        }
        // The captured 64-bit compactor aligns every allocated object to a
        // pointer boundary. Even, nonzero words alone do not establish this.
        if pointer % 8 != 0 {
            return Err("unaligned compacted Nat literal pointer".into());
        }
        if !self.gmp_bignums(pointer)? {
            return Err("heap Nat literal requires a captured v2 GMP region".into());
        }
        let header = self.header(pointer)?;
        if (header.tag, header.other) != (tags::MPZ, 0) {
            return Err("invalid compacted Nat literal MPZ header".into());
        }
        let counts = self.bytes(pointer, 8, 8)?;
        let allocated = i32::from_le_bytes(counts[..4].try_into().unwrap());
        let signed_size = i32::from_le_bytes(counts[4..].try_into().unwrap());
        if signed_size <= 0 || allocated != signed_size {
            return Err("noncanonical Nat literal MPZ allocation or sign".into());
        }
        let size = usize::try_from(signed_size).map_err(|_| "Nat literal limb count overflow")?;
        if size > MAX_LITERAL_LIMBS {
            return Err("Nat literal limb resource bound".into());
        }
        let bytes = size
            .checked_mul(8)
            .and_then(|n| n.checked_add(24))
            .ok_or("Nat literal byte size overflow")?;
        if usize::from(header.cs_sz) != bytes {
            return Err("noncanonical Nat literal MPZ object size".into());
        }
        let digits = self.word(pointer, 16)?;
        if digits != pointer.checked_add(24).ok_or("Nat literal limb pointer overflow")? {
            return Err("Nat literal MPZ limbs are not the captured inline payload".into());
        }
        let limbs = (0..size).map(|i| self.word(pointer, 24 + i * 8)).collect::<R<Vec<_>>>()?;
        if limbs.last() == Some(&0) || (size == 1 && limbs[0] <= u64::MAX >> 1) {
            return Err("noncanonical Nat literal MPZ magnitude".into());
        }
        // Preserve the existing JSON integer spelling when it is exact. Larger
        // values use a typed limb array, never a truncated integer or float.
        if size == 1 {
            Ok(json!(limbs[0]))
        } else {
            Ok(json!({"representation":"nat-limbs-le", "limbs":limbs}))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const BASE: u64 = 0x1000;
    const OFFSET: usize = 96;
    const POINTER: u64 = BASE + OFFSET as u64;

    fn mpz(limbs: &[u64]) -> Vec<u8> {
        let mut data = vec![0; OFFSET];
        data[..5].copy_from_slice(b"olean");
        data[5] = 2;
        data[6] = 1;
        data[7..13].copy_from_slice(b"4.27.0");
        data[40..80].fill(b'a');
        data[80..88].copy_from_slice(&BASE.to_le_bytes());
        data.extend_from_slice(&0u32.to_le_bytes());
        data.extend_from_slice(&((24 + limbs.len() * 8) as u16).to_le_bytes());
        data.extend_from_slice(&[0, tags::MPZ]);
        data.extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        data.extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        data.extend_from_slice(&(POINTER + 24).to_le_bytes());
        for limb in limbs {
            data.extend_from_slice(&limb.to_le_bytes());
        }
        data
    }

    fn view(data: &[u8], accesses: usize) -> View<'_> {
        View {
            regions: vec![("fixture", BASE, data)],
            budget: Cell::new(accesses),
            array_limit: 100,
            name_mode: NameMode::Lean,
        }
    }

    #[test]
    fn scalar_and_single_limb_literals_preserve_exact_u64() {
        let empty = view(&[], 0);
        for n in [0, 1, 53, u64::MAX >> 1] {
            assert_eq!(empty.literal_nat((n << 1) | 1).unwrap(), json!(n));
        }
        assert!(empty.literal_nat(0).is_err());
        for n in [1u64 << 63, u64::MAX] {
            let data = mpz(&[n]);
            let v = view(&data, 5);
            assert_eq!(v.literal_nat(POINTER).unwrap().as_u64(), Some(n));
            assert_eq!(v.budget.get(), 0);
        }
    }

    #[test]
    fn multi_limb_literals_remain_distinct_above_u64() {
        for limbs in [vec![0, 1], vec![1, 1], vec![u64::MAX, 1], vec![7, 0, 1], vec![17, 1, 1]] {
            let data = mpz(&limbs);
            let decoded = view(&data, 100).literal_nat(POINTER).unwrap();
            assert_eq!(decoded, json!({"representation":"nat-limbs-le", "limbs":limbs}));
            assert!(decoded.as_f64().is_none());
            let encoded = serde_json::to_string(&decoded).unwrap();
            assert_eq!(serde_json::from_str::<Value>(&encoded).unwrap(), decoded);
        }
    }

    #[test]
    fn literal_support_does_not_expand_index_carrier() {
        let data = mpz(&[0, 1]);
        let v = view(&data, 100);
        assert!(v.literal_nat(POINTER).is_ok());
        assert!(v.nat(POINTER).is_err());
    }

    #[test]
    fn malformed_mpz_layouts_signs_and_magnitudes_refuse() {
        for mutation in 0..13 {
            let mut data = mpz(&[0, 1]);
            match mutation {
                0 => data[OFFSET] = 1,     // nonzero reference count
                1 => data[OFFSET + 6] = 1, // boxed field in scalar object
                2 => data[OFFSET + 7] = tags::STRING,
                3 => data[OFFSET + 4..OFFSET + 6].copy_from_slice(&32u16.to_le_bytes()),
                4 => data[OFFSET + 8..OFFSET + 12].copy_from_slice(&3i32.to_le_bytes()),
                5 => data[OFFSET + 12..OFFSET + 16].copy_from_slice(&(-2i32).to_le_bytes()),
                6 => data[OFFSET + 12..OFFSET + 16].copy_from_slice(&0i32.to_le_bytes()),
                7 => data[OFFSET + 16..OFFSET + 24].copy_from_slice(&(POINTER + 32).to_le_bytes()),
                8 => data[OFFSET + 32..OFFSET + 40].fill(0),
                9 => {
                    data.pop();
                }
                10 => data[6] = 0,
                11 => data[6] = 3,
                _ => data[5] = 1,
            }
            assert!(view(&data, 100).literal_nat(POINTER).is_err(), "mutation {mutation}");
        }
        for small in [0, 1, u64::MAX >> 1] {
            assert!(view(&mpz(&[small]), 100).literal_nat(POINTER).is_err());
        }
    }

    #[test]
    fn literal_limbs_are_charged_and_allocation_is_bounded() {
        let data = mpz(&[0, 1]);
        assert!(view(&data, 5).literal_nat(POINTER).unwrap_err().contains("resource bound"));
        let v = view(&data, 6);
        assert!(v.literal_nat(POINTER).is_ok());
        assert_eq!(v.budget.get(), 0);
        assert!(v.literal_nat(POINTER).is_err());
        let mut limbs = vec![0; MAX_LITERAL_LIMBS];
        *limbs.last_mut().unwrap() = 1;
        assert!(view(&mpz(&limbs), MAX_LITERAL_LIMBS + 4).literal_nat(POINTER).is_ok());
        limbs.push(1);
        assert!(
            view(&mpz(&limbs), MAX_LITERAL_LIMBS + 10)
                .literal_nat(POINTER)
                .unwrap_err()
                .contains("limb resource bound")
        );
    }

    #[test]
    fn shifted_well_formed_mpz_payloads_are_not_aligned_objects() {
        for shift in [2usize, 4, 6] {
            let mut data = mpz(&[0, 1]);
            data.splice(OFFSET..OFFSET, vec![0; shift]);
            let pointer = POINTER + shift as u64;
            data[OFFSET + shift + 16..OFFSET + shift + 24]
                .copy_from_slice(&(pointer + 24).to_le_bytes());
            assert!(view(&data, 100).literal_nat(pointer).unwrap_err().contains("unaligned"));
        }
    }

    #[test]
    fn actual_literal_node_uses_lossless_nat_decoder() {
        let mut data = mpz(&[0, 1]);
        let literal = BASE + data.len() as u64;
        data.extend_from_slice(&[0, 0, 0, 0, 16, 0, 1, 0]);
        data.extend_from_slice(&POINTER.to_le_bytes());
        let value = view(&data, 100).literal(literal).unwrap();
        assert_eq!(
            value,
            node("num", vec![json!({"representation":"nat-limbs-le", "limbs":[0,1]})])
        );
    }
}
