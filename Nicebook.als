sig NiceBook{
	userContainsContent: User-> set Content,
	people: set User
	// userHasWall: User->one Wall
}

sig User{
	addCommentPrivacy: User -> PrivacyLevel,
	otherContentPrivacy: Content -> PrivacyLevel,
	myContentPrivacy: Content -> PrivacyLevel,
	friends: set User
}

sig Wall{
	wallOwner: one User,
	contains: set Content
}

abstract sig Content{
	contentOwner: one User,
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

pred contentInvariant[c: Content]{
	// some w : Wall | c.status = Published implies c in w.contains
}

pred nicebookInvariant[n:NiceBook]{
	// all c: Content|	c.status != UnUploaded implies c.contentOwner->c in n.userContainsContent
	// all u: User| u in n.people
	all c: Content | 
		some w: Wall | c in w.contains implies c.contentOwner -> c in n.userContainsContent
}

pred userInvariant[u:User]{
    //As a user, I must be the friend of my friends
    // all u':User | u' in u.friends implies u in u'.friends
    all u':u.friends | u in u'.friends

    //As a user, I cannot be my own friend
    u not in u.friends 

    // Each user has only one wall
    one w: Wall | u in w.wallOwner
}

pred photoInvariant[p:Photo]{
	// a photo can not be contained by 2 note
	all n, n': Note | p in n.notePhotos and p in n'.notePhotos implies n = n'

	// a photo can not be contained by 2 wall
	all w, w': Wall | p in w.contains and p in w'.contains implies w = w'
}

pred noteInvariant[n: Note]{
	// a photo can not be contained by 2 note
	// all n': Note | n.notePhotos = n'.notePhotos implies n = n'

	// a note can not be contained by 2 wall
	all w, w': Wall | n in w.contains and n in w'.contains implies w = w'
}

pred commentInvariant[c: Comment]{
    c not in c.^commentAttached
    some content : Content | 
		content not in Comment and 
		content in c.^commentAttached
    
    //As a comment, I must attach to a piece of content, but that content cannot be itself
    //c not in c.*commentAttached
    //As a comment, I can only attach to the content of my owner or my owner's friends
    one content: c.commentAttached | 
	one user : content.contentOwner | 
		c.contentOwner in user.friends or c.contentOwner in user
    //TODO As a comment, I must have a privacy setting that determines who is able to view me 

    // a comment can only be contained by one wall
    all w, w': Wall | c in w.contains and c in w'.contains implies w = w'
}

pred tagInvariant[t:Tag]{
//	one t.tagUser	
//	one t.tagAssociated

    //As a tag, I must associate to a note or a photo
    all comment: Comment| comment not in t.tagAssociated

    //As a tag, I must reference to a user, and that user must be my owner's friends
    all user: t.tagUser | user in t.tagAssociated.contentOwner.friends

    // no duplicate tag Assumption!
    all t': Tag |
	t'.tagUser = t.tagUser and
	t'.tagAssociated = t.tagAssociated implies
		t' = t
}

pred wallInvariant[w:Wall]{
	//As a wall, my content must be from my owner or my owner's friends
	all content: w.contains | 
		content.contentOwner in w.wallOwner or
		content.contentOwner in w.wallOwner.friends

	//As a wall, my content must be published
	// all c: w.contains | c.status = Published

	// I feel like there is other things here, liek PhotoB should appear on A's
	// wall, if A attached a comment to PhotoB...?

	// everything that attached to/contained by the w.contains 
	// should be contained in w
	all c : w.contains | 
		all content: c.notePhotos + notePhotos.c + get_all_comments[c] + get_all_related_contents[c] | 
			content in w.contains 
 
}

pred invariant[]{
    all u:User|userInvariant[u]
	all ct:Content|contentInvariant[ct]
    all p:Photo|photoInvariant[p]
    all n: Note| noteInvariant[n]
    all c:Comment|commentInvariant[c]
    all t:Tag|tagInvariant[t]
    all w:Wall|wallInvariant[w]
	all nb:NiceBook|nicebookInvariant[nb]
    //privacyInvariant
} 

//assert CheckAll {
//    // all c:Comment|commentInvariant[c]
//	all u:User|userInvariant[u]
//}

//check CheckAll for 3 but exactly 2 User, exactly 0 Photo, exactly 0 Comment
abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, EveryOne extends PrivacyLevel{}

// abstract sig PublishStatus{}
// one sig UnUploaded, Uploaded, Published extends PublishStatus{}

fun get_all_comments[c: Content]: set Comment{
	{m : Comment | c in m.^commentAttached}
}

fun get_all_related_contents[c: Content]: set Content{
	{c.^commentAttached}
}

pred upload[c: Content,u: User, n,n':NiceBook] {
	// pre condition
	u -> c not in n.userContainsContent

	// frame condition
	n'.people = n.people

	//post condition
	// some c' : Content | c'.contentOwner = c.contentOwner 
}

// assert uploadInvariant {
// 	all n, n': NiceBook, c:Content, u:User |
// 		nicebookInvariant[n] and upload[c,u,n,n'] implies
// 		nicebookInvariant[n']
// }

// check uploadInvariant for 10

run {
     invariant
 }for 5 but exactly 1 NiceBook,exactly 2 User, exactly 2 Photo, exactly 3 Comment, exactly 2 Note
