function identity<T>(x: T): T { return x; }
function firstOf<T>(xs: T[]): T { return xs[0]; }
const a = identity<number>(5);
const b = identity<string>("s");
const c = firstOf<number>([9, 8, 7]);
console.log(a, b, c);
