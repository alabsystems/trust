/// Other spellings of `<canon>/Lease.lock` (`canon` the directory's
/// canonical absolute path): case, `.`, `..`, `//`, `/var`.
pub(super) fn spelling_aliases(canon: &str) -> Vec<String> {
    let mut v = vec![
        "lease.LOCK".to_string(),
        "./Lease.lock".to_string(),
        "sub/../Lease.lock".to_string(),
        format!("{canon}//Lease.lock"),
    ];
    if let Some(rest) = canon.strip_prefix("/private") {
        v.push(format!("{rest}/Lease.lock"));
    }
    v
}
