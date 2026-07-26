const raw: unknown = "hello";
const s = raw as string;
const len = (s as string).length;
const arr = [1, 2, 3];
const n = arr.length as number;
const first = arr[0] as number;
const tag = ("x" as string) + (n as number);
console.log(s, len, n, first, tag);
