const Color = { Red: 0, Green: 1, Blue: 2 } as const;
type Color = (typeof Color)[keyof typeof Color];
function name(c: Color): string {
  return c === Color.Red ? "red" : c === Color.Green ? "green" : "blue";
}
console.log(Color.Green, name(Color.Blue), name(Color.Red));
