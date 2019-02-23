// The Die Hard Jugs problem
//
// You have two jugs, one 5 gallon, one 3 gallon.
// Fill one with exactly 4 gallons of water.
//
// You have no other measurement at hand.

open util/ordering[State]

sig State {
  big: Int,
  small: Int,
} {
  0 <= big
  big <= 5
  0 <= small
  small <= 3
}

pred FillSmall(s, s': State) {
  s'.small = 3
  s'.big = s.big
}

pred FillBig(s, s': State) {
  s'.big = 5
  s'.small = s.small
}

pred EmptySmall(s, s': State) {
  s'.small = 0
  s'.big = s.big
}

pred EmptyBig(s, s': State) {
  s'.big = 0
  s'.small = s.small
}

pred SmallToBig(s, s': State) {
  plus[s.big, s.small] <= 5 => {
    s'.big = plus[s.big, s.small]
    s'.small = 0
  } else {
    s'.big = 5
    s'.small = minus[s.small, minus[5, s.big]]
  }
}


pred BigToSmall(s, s': State) {
  plus[s.big, s.small] <= 3 => {
    s'.big = 0
    s'.small = plus[s.big, s.small]
  } else {
    s'.small = 3
    s'.big = minus[s.small, minus[3, s.big]]
  }
}

pred step(s, s': State) {
  FillSmall[s, s']
  or FillBig[s, s']
  or EmptySmall[s, s']
  or EmptyBig[s, s']
  or SmallToBig[s, s']
  or BigToSmall[s, s']
}

fact {
  first.big = 0
  first.small = 0
}

fact {
  all s: State, s': s.next | step[s, s']
}

run {
  last.big = 4
} for 7 State
