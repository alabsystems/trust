const rec: { a: number; b: string } = { a: 1, b: "z" };
const { a, b }: { a: number; b: string } = rec;
const [first, second]: [number, string] = [2, "w"];
function head({ x }: { x: number }): number { return x; }
console.log(a, b, first, second, head({ x: 99 }));
