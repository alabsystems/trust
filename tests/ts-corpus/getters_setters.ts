class Temperature {
  private c: number = 0;
  get celsius(): number { return this.c; }
  set celsius(value: number) { this.c = value; }
  get fahrenheit(): number { return this.c * 9 / 5 + 32; }
}
const t = new Temperature();
t.celsius = 25;
console.log(t.celsius, t.fahrenheit);
