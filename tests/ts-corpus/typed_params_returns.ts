function add(a: number, b: number): number { return a + b; }
function greet(who: string): string { return "hi " + who; }
function noop(): void {}
const total: number = add(add(1, 2), 3);
noop();
console.log(total, greet("x"));
