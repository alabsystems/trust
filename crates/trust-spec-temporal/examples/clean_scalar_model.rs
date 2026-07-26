// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Canonical complete-authority Clean scalar-model example. The same Clean
//! source is included by the crate's certification/replay tests so
//! documentation and executable behavior share one checked fixture.

use trust_spec_temporal::{certify_clean_scalar_model_with_ty, recheck_clean_scalar_model_with_ty};

const SOURCE: &str = include_str!("clean_scalar_complete.lean");

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let certificate =
        certify_clean_scalar_model_with_ty(SOURCE, "AuthorityExample.CompleteAuthority")?;
    recheck_clean_scalar_model_with_ty(&certificate, SOURCE)?;
    Ok(())
}
