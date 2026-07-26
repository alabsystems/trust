namespace Outer { export const a = 1; export namespace Inner { export const b = 2; export function sum(): number { return b + 10; } } }
console.log(Outer.a, Outer.Inner.b, Outer.Inner.sum());
console.log(JSON.stringify(Outer));
