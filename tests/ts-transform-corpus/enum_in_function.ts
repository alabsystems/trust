enum State { Idle, Running, Done }
function advance(s: State): State { return s === State.Done ? State.Idle : s + 1; }
console.log(advance(State.Idle), advance(State.Running), advance(State.Done));
console.log(State[advance(State.Idle)]);
