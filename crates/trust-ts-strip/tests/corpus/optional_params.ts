function tag(name: string, suffix?: string): string {
  return suffix ? name + suffix : name;
}
function scale(x: number, factor: number = 2): number { return x * factor; }
console.log(tag("a"), tag("a", "!"), scale(5), scale(5, 3));
