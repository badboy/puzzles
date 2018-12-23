// Can you solve the code for the lock?

abstract sig Digit {}

one sig Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine extends Digit {}

one sig Lock {
	p0: one Digit,
	p1: one Digit,
	p2: one Digit
}

pred lockHas(d: Digit) {
	Lock.p0 = d or Lock.p1 = d or Lock.p2 = d
}

// Clue #1: 682 – One number is correct and well placed
fact Clue1 {
	lockHas[Six] or lockHas[Eight] or lockHas[Two]

	lockHas[Six] implies Lock.p0 = Six and not lockHas[Eight] and not lockHas[Two]
	lockHas[Eight] implies Lock.p1 = Eight and not lockHas[Six] and not lockHas[Two]
	lockHas[Two] implies Lock.p2 = Two and not lockHas[Six] and not lockHas[Eight]
}

// Clue #2: 614 – One number is correct but wrongly placed
fact Clue2 {
	lockHas[Six] or lockHas[One] or lockHas[Four]

	lockHas[Six] implies Lock.p0 != Six and not lockHas[One] and not lockHas[Four]
	lockHas[One] implies Lock.p1 != One and not lockHas[Six] and not lockHas[Four]
	lockHas[Four] implies Lock.p2 != Four and not lockHas[Six] and not lockHas[One]
}

// Clue #3: 206 – Two numbers are correct but both are wrongly placed
fact Clue3 {
	(lockHas[Two] and lockHas[Zero]) or (lockHas[Two] and lockHas[Six]) or (lockHas[Zero] and lockHas[Six])

	(lockHas[Two] and lockHas[Zero]) implies Lock.p0 != Two and Lock.p1 != Zero
	(lockHas[Two] and lockHas[Six]) implies Lock.p0 != Two and Lock.p2 != Six
	(lockHas[Zero] and lockHas[Six]) implies Lock.p2 != Zero and Lock.p2 != Six
}

// Clue #4: 738 – None of the numbers are correct
fact Clue4 {
	not lockHas[Seven] and
	not lockHas[Three] and
	not lockHas[Eight]
}

// Clue #5: 780 – One number is correct but wrongly placed
fact Clue {
	lockHas[Seven] or lockHas[Eight] or lockHas[Zero]

	lockHas[Seven] implies Lock.p0 != Seven and not lockHas[Eight] and not lockHas[Zero]
	lockHas[Eight] implies Lock.p1 != Eight and not lockHas[Seven] and not lockHas[Zero]
	lockHas[Zero] implies Lock.p2 != Zero and not lockHas[Seven] and not lockHas[Eight]
}
