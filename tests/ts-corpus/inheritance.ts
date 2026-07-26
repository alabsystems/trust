class Animal {
  protected readonly name: string;
  constructor(name: string) { this.name = name; }
  speak(): string { return this.name + " makes a sound"; }
}
class Dog extends Animal {
  constructor(name: string) { super(name); }
  speak(): string { return this.name + " barks"; }
}
const a: Animal = new Dog("Rex");
console.log(a.speak(), a instanceof Dog, a instanceof Animal);
