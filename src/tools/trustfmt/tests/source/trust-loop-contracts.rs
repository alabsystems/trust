fn ordered(mut n:u32, limit:u32)->u32 {
'outer: while n<limit
// kept before the first clause
decreases /* kept after the keyword */ limit-n by Clean /* identity */ . Lemmas . dec
// kept between clauses
invariant n<=limit by Clean.Lemmas.bound
invariant forall i: usize,
    i<n ==> i<limit
invariant n'>=n
// kept after the final clause
{
n+=1;
if n>100 {break 'outer;}
}
n
}

fn nested(mut m:u8) {
let mut values=vec![1,2,3].into_iter();
while let Some(value)=values.next()
invariant value<=3
{
let mut step=|| {
while m<2 invariant m<=2 by Clean.Lemmas.inv decreases 2-m by Clean.Lemmas.dec {m+=1;}
};
step();
}
}
