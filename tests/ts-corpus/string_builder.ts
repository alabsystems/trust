function repeatJoin(word: string, times: number): string {
  const acc: string[] = [];
  for (let i: number = 0; i < times; i++) { acc.push(`${word}${i}`); }
  return acc.join("|");
}
const label: string = `count=${3 + 4}`;
console.log(repeatJoin("x", 4), label, "ab".repeat(3), "  hi  ".trim());
