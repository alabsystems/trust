function day(n: number): string {
  switch (n) {
    case 0: return "sun";
    case 6: return "sat";
    default: return "weekday";
  }
}
let out: string = "";
for (let i: number = 0; i < 7; i++) { out += day(i)[0]; }
console.log(day(0), day(3), day(6), out);
