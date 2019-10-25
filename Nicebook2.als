sig NiceBook{
	contents: User-> set Content,
	friends: User -> set User,
	people: set User,
	// userHasWall: User->one Wall
	wallContainer: Wall-> set Content
}

sig User{
}

sig Wall{
	wallOwner: one User,
	privacySetting: one PrivacyLevel,
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

/**Assumption**/
//if the content(note/photo) is unpublished, then it can not contains comments
pred contentInvariant[nb: NiceBook]{
	// no two users can have same content
	all u, u' : nb.people, c: Content | 
		u -> c in nb.contents and 
		u' -> c in nb.contents implies
			u' = u

	// if this piece of content (if note/photo) can not appear on other's wall
	// if it is not on its owner's wall
	// however, we do not consider comment here because A can comment
	// on B's comtent and that will only appear on B's wall

	all c : nb.contents[nb.people] |
		c not in Comment and c not in nb.wallContainer[(wallOwner.((nb.contents).c))] implies 
		((all w: wallOwner.(nb.people) | c not in nb.wallContainer[w]))
}

pred photoInvariant[nb: NiceBook]{
	// a photo can not be contained by 2 note
	 all p :  Photo | 
		all n, n':  Note | 
			p in n.notePhotos and p in n'.notePhotos implies n = n'

	// a photo can not be contained by 2 wall
	//all p :  nb.contents[nb.people] & Photo | 
//		all w, w': wallOwner.(nb.people) | 
//			p in w.contains and p in w'.contains implies w = w'

	// every note that contains photo (in content) should be in the content map
	all p: nb.contents[nb.people] & Photo |
		notePhotos.p in nb.contents[nb.people]
}

pred noteInvariant[nb : NiceBook]{
	// a note can not be contained by 2 wall
//	all n :  nb.contents[nb.people] & Note | 
//		all w, w': wallOwner.(nb.people) | 
//			n in w.contains and n in w'.contains implies w = w'

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
    	//all c:  nb.contents[nb.people] & Comment | 
//		all w, w': wallOwner.(nb.people) | 
//			c in w.contains and c in w'.contains implies w = w'

	all c:  nb.contents[nb.people] & Comment | 
		c in nb.wallContainer[wallOwner.(nb.people)]
}

pred tagInvariant[nb: NiceBook]{
    //As a tag, I must associate to a note or a photo
    all comment: Comment, t:Tag| comment not in t.tagAssociated

	// a tag can nonly be attached to published stuff /**Assumption**/
	all t: Tag | 
		t.tagAssociated in nb.wallContainer[(wallOwner.(nb.people))]

    	//As a tag, I must reference to a user, and that user must be my owner's friends
    	all t: Tag, u: nb.people | 
		u = t.tagUser implies u in nb.friends[nb.contents.(t.tagAssociated)]

		/**Assumption**/	
		// no duplicate tag !
    	all t, t':  tagAssociated.(nb.contents[nb.people]) |
		t'.tagUser = t.tagUser and
		t'.tagAssociated = t.tagAssociated implies
			t' = t
}

pred wallInvariant[nb: NiceBook]{
	// each user has only one wall
	// all u: nb.people | one w: wallOwner.(nb.people) | u = w.wallOwner
 	all u: nb.people | one wallOwner.u
	// Everything on the wall in the Nicebook should be in the map of u->c
	// As a wall, my content must be from my owner or my owner's friends
	all u: nb.people | 
		all c: nb.wallContainer[(wallOwner.u)] |
			c in User.(nb.contents) and
			((nb.contents).c = u or (nb.contents).c in nb.friends[u]) and 
			(c not in Comment implies (nb.contents).c = u)

	// I feel like there is other things here, liek PhotoB should appear on A's
	// wall, if A attached a comment to PhotoB...?

	// everything that attached to/contained by the w.contains 
	// should be contained in w
	all w: wallOwner.(nb.people) |
		all c : nb.wallContainer[w] | 
			all content: c.notePhotos + notePhotos.c + get_all_related_contents[c] | //get_all_comments[c]
				content in nb.wallContainer[w] 

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

fun get_unpublished_content_for_user[nb: NiceBook, u: User] : set Content{
	{
		c: Content | 
			c in nb.contents[u] and 
			c not in nb.wallContainer[(wallOwner.u)]//and
			//u in nb.people
	}
}

fun get_comment_from_content[c: Content] : set Comment{
	{comment: Comment | c in comment.^commentAttached}
}


/** following are operations **/
pred preUploadAndPublish[nb,nb':NiceBook,u:User, c:Content]{

	// pre-condition

	// FORGET THAT!->common sense, c should not have comment
	// no commentAttached.c

	// user is in NiceBook
	u in nb.people

    // no tag associated to that content

    no tagAssociated.c 

	// frame condition
	nb'.people = nb.people
	nb'.friends = nb.friends
}

/**upload operations**/
pred upload_note[nb, nb': NiceBook, u: User, c: Content]{
	// photos included in this note should be able to upload
	all p: c.notePhotos |
		p not in nb.contents[nb.people]

	nb'.contents = nb.contents + u->c + 
		{user: User, p:Photo|user=u and p in c.notePhotos}
}

pred upload_photo[nb, nb': NiceBook, u: User, c: Content]{
	// this photo should not be contained by a note
	no notePhotos.c
	nb'.contents = nb.contents + u->c
}


// ***Assumption no upload comment function ***/

// pred upload_comment[nb, nb': NiceBook, u: User, c: Content]{
// 	// for convenience, the comment can only be upload to a
// 	// uploaded but unpublished content and due to this, the 
// 	// target content's user should be same
// 	// if the target content is published, then this should be 
// 	// completed in publish op
// 	c.commentAttached in get_unpublished_content_for_user[nb, u]
// 	nb'.contents = nb.contents + u->c
// }

pred upload[nb, nb': NiceBook, u: User, c: Content]{
	// Assume one can only upload content that is the highest level
	// e.g. if you want to upload a photo that is contained by a note
	// in this case, you should upload the note

	// pre-condition & frame condtion
    
    // c does not in NiceBook
	c not in nb.contents[nb.people]

	c not in Comment

    preUploadAndPublish[nb,nb',u,c]

	nb'.wallContainer=nb.wallContainer
	//post-condition, add c based on its type
	(c in Note and upload_note[nb, nb', u, c]) or
	(c in Photo and upload_photo[nb, nb', u, c])

}

	/**add comment operations**/
pred addComment[nb,nb' : NiceBook, u:User, c:Content,comment: Comment]{
	/**pre-condition**/

	//that user should have permission to add comment according to privacy settings
	u in getUserWhoCanView[nb,wallOwner.((nb.contents).c)]

	//that content should be in the wall, which means that content is published
	c in nb.wallContainer[wallOwner.(nb.people)]

	//if c does not in Nicebook upload them
	//if c already uploaded, skip this upload but make sure that 
	// (comment not in nb.contents[nb.people] and upload[nb,nb',u,comment]) or
	// (comment in nb.contents[u] and preUploadAndPublish[nb,nb',u,comment] 
	// 	and nb'.contents=nb.contents and comment not in (nb.wallContainer[wallOwner.(nb.people)]) 

	c in comment.commentAttached

	nb'.contents=nb.contents+u->comment
	nb'.wallContainer=nb.wallContainer+{w: (nb.wallContainer).c, cm: Comment | cm = comment}

    nb'.people=nb.people
    nb'.friends=nb.friends
}

run addComment for 3

assert addCommentPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content,comment:Comment |
		invariant[nb] and addComment[nb,nb',u,c,comment] implies
		invariant[nb']
}

check addCommentPreserveInvariant for 3

run upload for 3

assert UploadPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content |
		invariant[nb] and upload[nb,nb',u,c] implies
		invariant[nb']
}

check UploadPreserveInvariant for 7

	/**remove operations**/

	
pred remove_note[nb, nb': NiceBook, u: User, c: Content]{
	// everything belong to this note is unpublished
	// note's photo
	all p: c.notePhotos | p not in nb.wallContainer[(wallOwner.u)]
	//note's comment
	// get_comment_from_content[c] not in (wallOwner.u).contains
	// note's photo's comment
	// all p: c.notePhotos |
	// 	get_comment_from_content[p]	not in (wallOwner.u).contains

	// remove note and everything belong to it
	nb'.contents = nb.contents - u->c -
		{user: User, p:Photo | user = u and p in c.notePhotos}
		// {
		// 	user: User, cm: Comment | user=(nb.contents).cm and cm in 
		// 		(get_comment_from_content[c] +
		// 		{pcm: Comment| all p: c.notePhotos | pcm in get_comment_from_content[p]})
		// }
}

pred remove_photo[nb, nb': NiceBook, u: User, c: Content]{
	//No note contains photo, if there is a note, then you should remove note
	no notePhotos.c

	
	//Remove all photo's comment
	// get_comment_from_content[c]	not in nb.wallContainer[(wallOwner.u)]
	
	//Remove photo and everything belong to it
	nb'.contents = nb.contents - u->c

}

//Assumption: only remove unpublished thing
pred remove[nb, nb': NiceBook, u: User, c: Content]{
	// pre condition
	// uploaded but not published, user is in NiceBook
	u in nb.people and u->c in nb.contents and
		c not in nb.wallContainer[(wallOwner.u)]

	// c is not a comment
	c not in Comment

	// post condition, remove c based on its type
	(c in Note and remove_note[nb, nb', u, c]) or
	(c in Photo and remove_photo[nb, nb', u, c])

	// frame condition
	nb'.people = nb.people
	nb'.friends = nb.friends
	nb'.wallContainer=nb.wallContainer
}

run remove for 5

assert RemovePreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content |
		invariant[nb] and remove[nb,nb',u,c] implies
		invariant[nb']
}

check RemovePreserveInvariant for 5

	/**publish operations**/


pred publish_note[nb,nb':NiceBook, u:User, c:Content, w:Wall]{
   	// photos included in this note should be able to publish
    all p:c.notePhotos |
		p in nb.contents[u] and 
		p not in nb.wallContainer[(wallOwner.(nb.people))]

	nb'.wallContainer=nb.wallContainer+w->c+
		{wall: Wall,p:Photo|wall=w and p in c.notePhotos}
}

pred publish_photo[nb,nb':NiceBook, u:User, c:Content, w:Wall]{
    // this photo should not be contained by a note
    no notePhotos.c

	nb'.wallContainer=nb.wallContainer+w->c

}

pred publish[nb,nb' : NiceBook, u:User, c:Content, w:Wall]{

	/**pre-condition**/

    //only wall owner can publish content things on their wall
    w.wallOwner in u
	//can't publish comment
	c not in Comment

	//if c does not in Nicebook upload them
	//if c already uploaded, skip this upload but make sure that 
	(c not in nb.contents[nb.people] and upload[nb,nb',u,c]) or
	(c in nb.contents[u] and preUploadAndPublish[nb,nb',u,c] 
		and nb'.contents=nb.contents and c not in (nb.wallContainer[wallOwner.(nb.people)])) 

	/**post-condition**/
	//publish c based on its type
	(c in Note and publish_note[nb, nb', u, c,w]) or
	(c in Photo and publish_photo[nb, nb', u, c,w]) 

    nb'.people=nb.people
    nb'.friends=nb.friends
}

run publish for 7

assert PublishPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content, w:Wall |
		invariant[nb] and publish[nb,nb',u,c,w] implies
		invariant[nb']
}

check PublishPreserveInvariant for 7

fun getUserWhoCanView[nb:NiceBook, w: Wall]: set User{
	w.privacySetting=EveryOne implies {nb.people} 
	
	else w.privacySetting=FriendsOfFriends implies {nb.friends[nb.friends[w.wallOwner]]+nb.friends[w.wallOwner]+w.wallOwner} //Default All User

	else w.privacySetting=Friends implies {nb.friends[w.wallOwner]+w.wallOwner} //Default All User
	
	else {w.wallOwner}
}

fun viewable[nb:NiceBook,u:User]:set Content{
	{c:nb.contents[nb.people]|
		u in getUserWhoCanView[nb,wallOwner.((nb.contents).c)]
		and (some w:wallOwner.(nb.people)| c in nb.wallContainer[w])}
}

run {
	all nb: NiceBook | invariant[nb]
} for 5 but exactly 1 NiceBook, exactly 4 User, exactly 2 Note, exactly 3 Comment, exactly 2 Photo
