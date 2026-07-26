use std::io::{self, Write};

pub(crate) fn process_signal_semantics_boundary() -> io::Result<()> {
    let mut out = std::io::stdout();
    out.write_all(b"fixture stdout boundary\n")?;
    println!("fixture stdout line");
    Ok(())
}
