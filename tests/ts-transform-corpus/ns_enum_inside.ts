namespace Traffic { export enum Signal { Red, Yellow, Green } export function next(s: Signal): Signal { return (s + 1) % 3; } }
console.log(Traffic.Signal.Red, Traffic.Signal.Green, Traffic.next(Traffic.Signal.Red));
console.log(Traffic.Signal[2]);
