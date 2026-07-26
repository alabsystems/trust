type A = { a: number };
type B = { b: string };
function combine(x: A & B): string { return x.a + x.b; }
function pickId(x: number | string): string { return String(x); }
const both: A & B = { a: 1, b: "z" };
console.log(combine(both), pickId(5), pickId("q"));
