const wrap = <T,>(x: T): T[] => [x];
const pick = <T, U>(a: T, _b: U): T => a;
console.log(wrap<number>(5).length, wrap("a")[0], pick<number, string>(1, "z"));
