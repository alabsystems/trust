fn default_return(x:u32)
requires x > 0
ensures result == ()
{let _=x;}

fn cited(by:u32)->u32
requires by == by
ensures foo(by)==by by Clean /* identity comment */ . Lemmas . /* spelling */ bound
{by}

fn interleaved<T>(x:&mut T, value:T)
ensures x' == value
requires true
ensures result == ()
where T:Copy
{*x=value}

fn ordered(xs:&[u32])->bool
requires forall i j: usize, i < j && j < xs.len() ==> xs[i] <= xs[j]
ensures result
{true}

fn find(xs:&[u32], needle:u32)->Option<usize>
requires if xs.is_empty() { needle == 0 } else { true }
ensures match result {
    Some(i) => i < xs.len(),
    None => true,
}
{xs.iter().position(|value|*value==needle)}

trait Contracted {
fn required(&self)->bool
requires true
ensures result;

fn notify(&self)
requires true;
}

struct Service;

impl Service {
fn run(&self, value:u32)->u32
ensures result == value
requires value > 0
{value}
}

extern "C" {
fn foreign(value:u32)->u32
requires value > 0
ensures result > 0;
}

fn commented(value:u32)->u32
// kept before the first clause
requires /* kept after the keyword */ value > 0
// kept between clauses
ensures result == value
// kept after the final clause
{value}
