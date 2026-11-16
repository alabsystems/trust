//! Model-v3 actual environment identity. Preserve the legacy complete metadata
//! inventory and budgets; encode only the fixed CLOSED theorem type/body pairs
//! with the same bounded canonical CIC codec used to retain them. No label or
//! supplied digest replaces any actual declaration or checked proof bytes.
use std::collections::BTreeSet;
use std::io::{self, Write};

use clean_kernel::{Environment, Name};
use sha2::{Digest, Sha256};

use super::TermPacket;

fn frame_names() -> BTreeSet<Name> {
    let mut names = BTreeSet::new();
    for k in [8, 16, 24, 32, 40, 48, 56] {
        names.insert(Name::from_string(&format!("Clean.FrameByteShiftV1.shl{k}")));
    }
    for i in 1..16 {
        for j in 0..i {
            names.insert(Name::from_string(&format!("Clean.FrameOffsetsV1.distinct{i}_{j}")));
        }
    }
    for q in 0..16 {
        names.insert(Name::from_string(&format!("Clean.FrameReadV1.byte{q}")));
    }
    for which in 0..2 {
        for n in 1..=8 {
            names.insert(Name::from_string(&format!(
                "Clean.FrameWordTransportV1.word{which}_prefix{n}"
            )));
        }
    }
    names.insert(Name::from_string("Clean.FrameWordAssemblyV1.reconstruct"));
    names
}
struct HashWriter {
    hash: Sha256,
    row: usize,
    total: usize,
}
impl Write for HashWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.row = self
            .row
            .checked_add(bytes.len())
            .ok_or_else(|| io::Error::other("frame environment row overflow"))?;
        self.total = self
            .total
            .checked_add(bytes.len())
            .ok_or_else(|| io::Error::other("frame environment total overflow"))?;
        if self.row > 8 * 1024 * 1024 || self.total > 64 * 1024 * 1024 {
            return Err(io::Error::other("frame environment serialization budget"));
        }
        self.hash.update(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
pub(super) fn digest(env: &Environment) -> Result<String, String> {
    let mut names = BTreeSet::new();
    for name in env
        .constants()
        .map(|x| &x.name)
        .chain(env.inductives().map(|x| &x.name))
        .chain(env.constructors().map(|x| &x.name))
        .chain(env.recursors().map(|x| &x.name))
        .chain(env.quotients().map(|x| &x.name))
    {
        if names.len() >= 8192 {
            return Err("frame environment population budget".into());
        }
        names.insert(name.clone());
    }
    let frames = frame_names();
    if frames.len() != 160 || !frames.is_subset(&names) {
        return Err("frame environment complete fixed theorem population".into());
    }
    let mut w = HashWriter { hash: Sha256::new(), row: 0, total: 0 };
    serde_json::to_writer(&mut w, &("original-BVC-frame-environment/v3", env.mode(), names.len()))
        .map_err(|e| e.to_string())?;
    for name in names {
        w.row = 0;
        let fields = env.get_structure_field_names(&name);
        let defaults: Vec<_> = fields
            .unwrap_or(&[])
            .iter()
            .map(|f| (f, env.get_structure_field_default(&name, f)))
            .collect();
        // Every non-expression ConstantInfo field remains in the identity. Both
        // actual expressions are captured; the fixed source packet is not rehashed
        // in lieu of inspecting the actual declaration installed in this env.
        if frames.contains(&name) {
            let info = env.get_const(&name).ok_or("frame theorem declaration missing")?;
            // Deliberately exhaustive: an added ConstantInfo field must fail to compile
            // until the identity includes it, rather than silently omit new metadata.
            let clean_kernel::ConstantInfo {
                name: actual_name,
                level_params,
                type_,
                value,
                is_reducible,
                reducibility,
                kind,
            } = info;
            let packet = TermPacket::capture(
                type_,
                value.as_ref().ok_or("frame theorem has no proof value")?,
            )?;
            serde_json::to_writer(
                &mut w,
                &(
                    "closed-theorem/CIC-DAG-v1",
                    &name,
                    actual_name,
                    level_params,
                    packet,
                    is_reducible,
                    reducibility,
                    kind,
                ),
            )
            .map_err(|e| e.to_string())?;
        } else {
            serde_json::to_writer(&mut w, &("base/raw-v1", &name, env.get_const(&name)))
                .map_err(|e| e.to_string())?;
        }
        serde_json::to_writer(
            &mut w,
            &(
                env.get_inductive(&name),
                env.get_constructor(&name),
                env.get_recursor(&name),
                env.get_quot(&name),
                env.get_constant_origin(&name),
                env.declaration_verification(&name),
                fields,
                defaults,
                env.get_structure_parents(&name),
                env.get_implemented_by(&name),
            ),
        )
        .map_err(|e| e.to_string())?;
    }
    Ok(format!("{:x}", w.hash.finalize()))
}
