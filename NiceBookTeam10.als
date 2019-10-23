sig NiceBook{
	contents: User-> set Content,
	friends: User -> set User,
	people: set User
	// userHasWall: User->one Wall
}

sig User{
	addCommentPrivacy: User -> PrivacyLevel,
	otherContentPrivacy: Content -> PrivacyLevel,
	myContentPrivacy: Content -> PrivacyLevel
//	friends: set User
}

sig Wall{
	wallOwner: one User,
	contains: set Content
}

abstract sig Content{
//	contentOwner: one User,
}

sig Note extends Content{
	notePhotos: set Photo
}

sig Photo extends Content{}

sig Comment extends Content{
	//As a comment, I must attach to a piece of content, 
	//but that content cannot be itself
	commentAttached: one Content
}

sig Tag{
	tagUser: one User,
	tagAssociated: one Content
}

abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, EveryOne extends PrivacyLevel{}

pred nicebookInvariant[nb: NiceBook]{
	// people contains all friends
	all u: nb.people | nb.friends[u] in nb.people

	// symmetric friendship
	all u, u' : User | u -> u' in nb.friends implies u' -> u in nb.friends

	// not friend of himself
	no u: User | u -> u in nb.friends

	// nicebook only contain contents of its people
	all u : User | u not in nb.people implies no nb.contents[u]
}

pred contentInvariant[nb: NiceBook]{
	// no two users can have same content
	all u, u' : nb.people, c: Content | 
		u -> c in nb.contents and 
		u' -> c in nb.contents implies
			u' = u
}

pred photoInvariant[nb: NiceBook]{
	// a photo can not be contained by 2 note
	 all p :  nb.contents[nb.people] & Photo | 
		all n, n':  nb.contents[nb.people] & Note | 
			p in n.notePhotos and p in n'.notePhotos implies n = n'

	// a photo can not be contained by 2 wall
	all p :  nb.contents[nb.people] & Photo | 
		all w, w': wallOwner.(nb.people) | 
			p in w.contains and p in w'.contains implies w = w'

	// every note that contains photo (in content) should be in the content map
	all p: nb.contents[nb.people] & Photo |
		notePhotos.p in nb.contents[nb.people]
}

pred noteInvariant[nb : NiceBook]{
	// a note can not be contained by 2 wall
	all n :  nb.contents[nb.people] & Note | 
		all w, w': wallOwner.(nb.people) | 
			n in w.contains and n in w'.contains implies w = w'

	// the owner of the note and the photo it contains should be same
	all n : nb.contents[nb.people] & Note, u: nb.people |
		u -> n in nb.contents implies
			(all p : n.notePhotos | u -> p in nb.contents)
}

pred commentInvariant[nb: NiceBook]{
	// comment can not be attached to itself and no loops
	all c': Comment | c' not in c'.^commentAttached
    
    	//As a comment, I can only attach to the content of my owner or visible on other's wall
	all c: nb.contents[nb.people] & Comment |
		c.commentAttached in nb.contents[nb.people]
       //TODO As a comment, I must have a privacy setting that determines who is able to view me 

       // a comment can only be contained by one wall
    	all c:  nb.contents[nb.people] & Comment | 
		all w, w': wallOwner.(nb.people) | 
			c in w.contains and c in w'.contains implies w = w'
}

pred tagInvariant[nb: NiceBook]{
    //As a tag, I must associate to a note or a photo
    all comment: Comment, t:Tag| comment not in t.tagAssociated

    //As a tag, I must reference to a user, and that user must be my owner's friends
    all t: Tag, u: User | 
	u = t.tagUser implies u in nb.friends[nb.contents.(t.tagAssociated)]

    // no duplicate tag Assumption!
    all t, t':  tagAssociated.(nb.contents[nb.people]) |
	t'.tagUser = t.tagUser and
	t'.tagAssociated = t.tagAssociated implies
		t' = t
}

pred wallInvariant[nb: NiceBook]{
	// each user has only one wall
	all u: nb.people | one w: wallOwner.(nb.people) | u = w.wallOwner

	// Everything on the wall in the Nicebook should be in the map of u->c
	// As a wall, my content must be from my owner or my owner's friends
	all u: nb.people | 
		all c: (wallOwner.u).contains |
			c in User.(nb.contents) and
			((nb.contents).c = u or (nb.contents).c in nb.friends[u])

	// I feel like there is other things here, liek PhotoB should appear on A's
	// wall, if A attached a comment to PhotoB...?

	// everything that attached to/contained by the w.contains 
	// should be contained in w
	all w: wallOwner.(nb.people) |
		all c : w.contains | 
			all content: c.notePhotos + notePhotos.c + get_all_comments[c] + get_all_related_contents[c] | 
				content in w.contains 
 
}

pred invariant[nb: NiceBook]{
	// just consider everything inside NiceBook nb,
	// anything else might be in the next state of nb or 
	// they might just be some rubbish but we do not care
    	nicebookInvariant[nb]
    	contentInvariant[nb]
    	photoInvariant[nb]
    	noteInvariant[nb]
    	commentInvariant[nb]
    	tagInvariant[nb]
    	wallInvariant[nb]
    	//privacyInvariant
} 

fun get_all_comments[c: Content]: set Comment{
	{m : Comment | c in m.^commentAttached}
}

fun get_all_related_contents[c: Content]: set Content{
	{c.^commentAttached}
}

run {
	all nb: NiceBook | invariant[nb]
} for 5 but exactly 1 NiceBook, exactly 4 User, exactly 2 Note, exactly 3 Comment, exactly 2 Photo
