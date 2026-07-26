type ID = number;
type Pair = [string, number];
type Handler = (value: number) => number;
const id: ID = 10;
const p: Pair = ["a", 1];
const h: Handler = (v: number): number => v * 2;
console.log(id, p[0], p[1], h(21));
