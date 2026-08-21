// Probe: instantiate bytesize's generic mutators so TRUST_DUMP_MONO=1 dumps
// the monomorphized bodies and their Into/From identity chain.
#[path = "/var/folders/t8/f940w1lj2dv2l9bmn9ccj3200000gn/T/tmp.CETwYNnKVP/bytesize-1.3.0/src/lib.rs"]
mod bytesize;
use bytesize::ByteSize;

fn main() {
    let mut b = ByteSize(1024);
    b += 512u64;
    b *= 2u64;
    b += ByteSize(1);
    std::hint::black_box(b);
}
