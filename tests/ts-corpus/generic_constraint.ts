interface Lengthy { length: number; }
function longest<T extends Lengthy>(a: T, b: T): T {
  return a.length >= b.length ? a : b;
}
function pluck<T, K extends keyof T>(o: T, k: K): T[K] { return o[k]; }
const obj = { name: "trust", size: 5 };
console.log(longest("aaa", "bb"), longest([1, 2], [3]).length, pluck(obj, "name"), pluck(obj, "size"));
