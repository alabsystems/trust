function sum(...nums: number[]): number {
  return nums.reduce((a: number, b: number): number => a + b, 0);
}
const base: number[] = [1, 2, 3];
const more: number[] = [...base, 4, 5];
const [head, ...tail]: number[] = more;
console.log(sum(...more), more.length, head, tail.join(","));
