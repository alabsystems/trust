function conv(x: number): string;
function conv(x: string): number;
function conv(x: number | string): string | number {
  return typeof x === "number" ? "n" + x : x.length;
}
console.log(conv(7), conv("abcd"));
