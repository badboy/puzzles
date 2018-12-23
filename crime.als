-- Who was the killer?
--
-- via https://xmonader.github.io/prolog/2018/12/21/solving-murder-prolog.html

abstract sig Person {
	weapon: one Weapon
}
abstract sig Man extends Person { }
abstract sig Woman extends Person {}

one sig George, John, Robert extends Man {}
one sig Barbara, Christine, Yolanda extends Woman {}

abstract sig Room {
	contains: one Person,
}
one sig Bathroom, Diningroom, Kitchen, Livingroom, Pantry, Study extends Room {}

abstract sig Weapon {}
one sig Bag, Firearm, Gas, Knife, Poison, Rope extends Weapon {}

fact SinglePersonPerRoom {
	all r, r': Room | r != r' implies r.contains != r'.contains
}
fact SingleWeaponPerPerson {
	all p, p': Person | p != p' implies p.weapon != p'.weapon
}


--  Clue 1: The man in the kitchen was not found with the rope, knife, or bag.
-- Which weapon, then, which was not the firearm, was found in the kitchen?
fact Clue1 {
	Kitchen.contains in Man
	Kitchen.contains.weapon not in Rope + Knife + Bag + Firearm
}

-- Clue 2:  Clue 2: Barbara was either in the study or the bathroom; Yolanda was in the other.
-- Which room was Barbara found in?
fact Clue2 {
	Study.contains = Barbara or Bathroom.contains = Barbara
	(Study + Bathroom).contains in Barbara+Yolanda
}

-- Clue 3: The person with the bag, who was not Barbara nor George, was not in the bathroom nor the dining room.
-- Who had the bag in the room with them?
fact Clue3 {
	Barbara.weapon != Bag
	George.weapon != Bag
	all p: Person, r: Room | p.weapon = Bag and r.contains in p implies not r in Bathroom+Diningroom
}

-- Clue 4: The woman with the rope was found in the study. Who had the rope?
fact Clue4 {
	Study.contains in Woman
	Study.contains.weapon = Rope
}

-- Clue 5: The weapon in the living room was found with either John or George. What weapon was in the living room?
fact Clue5 {
	Livingroom.contains in John + George
}

-- Clue 6: The knife was not in the dining room. So where was the knife?
fact Clue6 {
	Diningroom.contains.weapon != Knife
}


-- Clue 7: Yolanda was not with the weapon found in the study nor the pantry. What weapon was found with Yolanda?
fact Clue7  {
	not Yolanda in (Study + Pantry).contains
}

-- Clue 8: The firearm was in the room with George. In which room was the firearm found?
fact Clue8 {
	George.weapon = Firearm
}

-- Clue 9: It was discovered that Mr. Boddy was gassed in the pantry.
-- The suspect found in that room was the murderer. Who, then, do you point the finger towards?
fact Clue9 {
	Pantry.contains.weapon = Gas
}

