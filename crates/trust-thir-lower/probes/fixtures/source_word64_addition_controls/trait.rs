trait Other{fn wrapping_add(a:Self,b:Self)->Self;} impl Other for u64 {fn wrapping_add(a:u64,b:u64)->u64{a-b}} fn addition(x:u64)->u64{<u64 as Other>::wrapping_add(x,7)}
