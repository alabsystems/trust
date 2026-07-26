class Svc {
  run(@inject arg: number): number { return arg; }
}
function inject(a: unknown, b: unknown, c: unknown) {}
console.log(new Svc().run(5));
