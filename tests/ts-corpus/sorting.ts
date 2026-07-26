const words: string[] = ["pear", "apple", "fig", "cherry"];
const byLen: string[] = [...words].sort((a: string, b: string): number => a.length - b.length);
const nums: number[] = [5, 2, 8, 1, 9, 3];
const desc: number[] = [...nums].sort((a: number, b: number): number => b - a);
console.log(byLen.join(","), desc.join(","));
