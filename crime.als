-- Who was the killer?
--
-- via https://xmonader.github.io/prolog/2018/12/21/solving-murder-prolog.html

abstract sig Person {}
abstract sig Man extends Person { }
abstract sig Woman extends Person {}

one sig George, John, Robert extends Man {}
one sig Barbara, Christine, Yolanda extends Woman {}

abstract sig Room {
	containsHuman: one Person,
	found: one Weapon
}
one sig Bathroom, Diningroom, Kitchen, Livingroom, Pantry, Study extends Room {}

abstract sig Weapon {}
one sig Bag, Firearm, Gas, Knife, Poison, Rope extends Weapon {}

fact SinglePersonPerRoom {
	all r, r': Room | r != r' implies r.containsHuman != r'.containsHuman
}
fact SingleWeaponPerPerson {
	all r, r': Room | r != r' implies r.found != r'.found
}


--  Clue 1: The man in the kitchen was not found with the rope, knife, or bag.
-- Which weapon, then, which was not the firearm, was found in the kitchen?
fact Clue1 {
	Kitchen.containsHuman in Man
	not Rope in Kitchen.found
	not Knife in Kitchen.found
	not Bag in Kitchen.found
	not Firearm in Kitchen.found
}

-- Clue 2:  Clue 2: Barbara was either in the study or the bathroom; Yolanda was in the other.
-- Which room was Barbara found in?
fact Clue2 {
	Study.containsHuman in Barbara or Bathroom.containsHuman in Barbara

	Study.containsHuman in Barbara implies Bathroom.containsHuman in Yolanda
	Bathroom.containsHuman in Barbara  implies Study.containsHuman in Yolanda
}

-- Clue 3: The person with the bag, who was not Barbara nor George, was not in the bathroom nor the dining room.
-- Who had the bag in the room with them?
fact Clue3 {
	all r: Room | r.found in Bag implies not r.containsHuman in Barbara and not r.containsHuman in George
	not Bathroom.found in Bag
	not Diningroom.found in Bag
}

-- Clue 4: The woman with the rope was found in the study. Who had the rope?
fact Clue4 {
	Study.containsHuman in Woman
	Study.found in Rope
}

-- Clue 5: The weapon in the living room was found with either John or George. What weapon was in the living room?
fact Clue5 {
	Livingroom.containsHuman in John + George
}

-- Clue 6: The knife was not in the dining room. So where was the knife?
fact Clue6 {
	not Diningroom.found in Knife
}


-- Clue 7: Yolanda was not with the weapon found in the study nor the pantry. What weapon was found with Yolanda?
fact Clue7  {
	not Study.containsHuman in Yolanda
	not Pantry.containsHuman in Yolanda
}

-- Clue 8: The firearm was in the room with George. In which room was the firearm found?
fact Clue8 {
	all r: Room | r.containsHuman in George implies r.found in Firearm
}

-- Clue 9: It was discovered that Mr. Boddy was gassed in the pantry.
-- The suspect found in that room was the murderer. Who, then, do you point the finger towards?

fact Clue9 {
	Pantry.found in Gas
}


