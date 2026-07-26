namespace A { export namespace B { export namespace C { export const deep = 100; export function get(): number { return deep; } } } }
console.log(A.B.C.deep, A.B.C.get(), JSON.stringify(A));
