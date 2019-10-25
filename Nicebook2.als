sig NiceBook{
	hasContent: User-> set Content,
	hasFriends: User -> set User,
	hasPeople: set User,
	// userHasWall: User->one Wall
	contains: Wall-> set Content
}

sig User{
}

sig Wall{
	hasWallOwner: one User,
	hasPrivacySetting: one PrivacyLevel,
}

abstract sig Content{
//	contentOwner: one User,
}

sig Note extends Content{
	hasPhotos: set Photo
}

sig Photo extends Content{}

sig Comment extends Content{
	//As a comment, I must attach to a piece of content, 
	//but that content cannot be itself
	attachedTo: one Content
}

sig Tag{
	taggedUser: one User,
	associatedWith: one Content
}

abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, EveryOne extends PrivacyLevel{}

pred nicebookInvariant[nb: NiceBook]{
	// hasPeople contains all hasFriends
	all u: nb.hasPeople | nb.hasFriends[u] in nb.hasPeople

	// symmetric friendship
	all u, u' : User | u -> u' in nb.hasFriends implies u' -> u in nb.hasFriends

	// not friend of himself
	no u: User | u -> u in nb.hasFriends

	// nicebook only contain hasContent of its hasPeople
	all u : User | u not in nb.hasPeople implies no nb.hasContent[u]
}

/**Assumption**/
//if the content(note/photo) is unpublished, then it can not contains comments
pred contentInvariant[nb: NiceBook]{
	// no two users can have same content
	all u, u' : nb.hasPeople, c: Content | 
		u -> c in nb.hasContent and 
		u' -> c in nb.hasContent implies
			u' = u

	// if this piece of content (if note/photo) can not appear on other's wall
	// if it is not on its owner's wall
	// however, we do not consider comment here because A can comment
	// on B's comtent and that will only appear on B's wall

	all c : nb.hasContent[nb.hasPeople] |
		c not in Comment and c not in nb.contains[(hasWallOwner.((nb.hasContent).c))] implies 
		((all w: hasWallOwner.(nb.hasPeople) | c not in nb.contains[w]))
}

pred photoInvariant[nb: NiceBook]{
	// a photo can not be contained by 2 note
	 all p :  Photo | 
		all n, n':  Note | 
			p in n.hasPhotos and p in n'.hasPhotos implies n = n'

	// a photo can not be contained by 2 wall
	//all p :  nb.hasContent[nb.hasPeople] & Photo | 
//		all w, w': hasWallOwner.(nb.hasPeople) | 
//			p in w.contains and p in w'.contains implies w = w'

	// every note that contains photo (in content) should be in the content map
	all p: nb.hasContent[nb.hasPeople] & Photo |
		hasPhotos.p in nb.hasContent[nb.hasPeople]
}

pred noteInvariant[nb : NiceBook]{
	// a note can not be contained by 2 wall
//	all n :  nb.hasContent[nb.hasPeople] & Note | 
//		all w, w': hasWallOwner.(nb.hasPeople) | 
//			n in w.contains and n in w'.contains implies w = w'

	// the owner of the note and the photo it contains should be same
	all n : nb.hasContent[nb.hasPeople] & Note, u: nb.hasPeople |
		u -> n in nb.hasContent implies
			(all p : n.hasPhotos | u -> p in nb.hasContent)
}

pred commentInvariant[nb: NiceBook]{
	// comment can not be attached to itself and no loops
	all c': Comment | c' not in c'.^attachedTo
    
    	//As a comment, I can only attach to the content of my owner or visible on other's wall
	all c: nb.hasContent[nb.hasPeople] & Comment |
		c.attachedTo in nb.hasContent[nb.hasPeople]
       //TODO As a comment, I must have a privacy setting that determines who is able to view me 

       // a comment can only be contained by one wall
    	//all c:  nb.hasContent[nb.hasPeople] & Comment | 
//		all w, w': hasWallOwner.(nb.hasPeople) | 
//			c in w.contains and c in w'.contains implies w = w'

	all c:  nb.hasContent[nb.hasPeople] & Comment | 
		c in nb.contains[hasWallOwner.(nb.hasPeople)]

	// comment on some wall of NiceBook means it is on every wall of its container
 	all c: nb.contains[hasWallOwner.(nb.hasPeople)] & Comment | nb.contains.(c.attachedTo)->c in nb.contains
}

pred tagInvariant[nb: NiceBook]{
    //As a tag, I must associate to a note or a photo
    all comment: Comment, t:Tag| comment not in t.associatedWith

	// a tag can nonly be attached to published stuff /**Assumption**/
//	all t: Tag | 
//		t.associatedWith in nb.contains[(hasWallOwner.(nb.hasPeople))]

    	//As a tag, I must reference to a user, and that user must be my owner's hasFriends
    	all t: Tag, u: nb.hasPeople | 
		u = t.taggedUser and t.associatedWith in nb.hasContent[nb.hasPeople] implies u in nb.hasFriends[nb.hasContent.(t.associatedWith)]

		/**Assumption**/	
		// no duplicate tag !
    	all t, t':  associatedWith.(nb.hasContent[nb.hasPeople]) |
		t'.taggedUser = t.taggedUser and
		t'.associatedWith = t.associatedWith implies
			t' = t
}

pred wallInvariant[nb: NiceBook]{
	// each user has only one wall
	// all u: nb.hasPeople | one w: hasWallOwner.(nb.hasPeople) | u = w.hasWallOwner
 	all u: nb.hasPeople | one hasWallOwner.u
	// Everything on the wall in the Nicebook should be in the map of u->c
	// As a wall, my content must be from my owner or my owner's hasFriends

	all u: nb.hasPeople | 
		all c: nb.contains[(hasWallOwner.u)] |
			c in User.(nb.hasContent) and
			(c not in Comment implies ((nb.hasContent).c = u or (nb.hasContent).c in nb.hasFriends[u]))

	// I feel like there is other things here, liek PhotoB should appear on A's
	// wall, if A attached a comment to PhotoB...?

	// everything that attached to/contained by the w.contains 
	// should be contained in w
	all w: hasWallOwner.(nb.hasPeople) |
		all c : nb.contains[w] | 
			all content: c.hasPhotos + hasPhotos.c + c.(*attachedTo) | //get_all_related_contents[c] | //get_all_comments[c]
				content in nb.contains[w] 

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
	{m : Comment | c in m.^attachedTo}
}

fun get_all_related_contents[c: Content]: set Content{
	{c.^attachedTo}
}

fun get_unpublished_content_for_user[nb: NiceBook, u: User] : set Content{
	{
		c: Content | 
			c in nb.hasContent[u] and 
			c not in nb.contains[(hasWallOwner.u)]//and
			//u in nb.hasPeople
	}
}

fun get_comment_from_content[c: Content] : set Comment{
	{comment: Comment | c in comment.^attachedTo}
}


/** following are operations **/
pred preUploadAndPublish[nb,nb':NiceBook,u:User, c:Content]{

	// pre-condition

	// FORGET THAT!->common sense, c should not have comment
	// no attachedTo.c

	// user is in NiceBook
	u in nb.hasPeople

    // no tag associated to that content

    no associatedWith.c 
	no associatedWith.(c.hasPhotos)

	// frame condition
	nb'.hasPeople = nb.hasPeople
	nb'.hasFriends = nb.hasFriends
}

/**upload operations**/
pred upload_note[nb, nb': NiceBook, u: User, c: Content]{
	// photos included in this note should be able to upload
	all p: c.hasPhotos |
		p not in nb.hasContent[nb.hasPeople]

	nb'.hasContent = nb.hasContent + u->c + 
		{user: User, p:Photo|user=u and p in c.hasPhotos}
}

pred upload_photo[nb, nb': NiceBook, u: User, c: Content]{
	// this photo should not be contained by a note
	no hasPhotos.c
	nb'.hasContent = nb.hasContent + u->c
}


// ***Assumption no upload comment function ***/

// pred upload_comment[nb, nb': NiceBook, u: User, c: Content]{
// 	// for convenience, the comment can only be upload to a
// 	// uploaded but unpublished content and due to this, the 
// 	// target content's user should be same
// 	// if the target content is published, then this should be 
// 	// completed in publish op
// 	c.attachedTo in get_unpublished_content_for_user[nb, u]
// 	nb'.hasContent = nb.hasContent + u->c
// }

pred upload[nb, nb': NiceBook, u: User, c: Content]{
	// Assume one can only upload content that is the highest level
	// e.g. if you want to upload a photo that is contained by a note
	// in this case, you should upload the note

	// pre-condition & frame condtion
    
    // c does not in NiceBook
	c not in nb.hasContent[nb.hasPeople]

	c not in Comment

    preUploadAndPublish[nb,nb',u,c]

	nb'.contains=nb.contains
	//post-condition, add c based on its type
	(c in Note and upload_note[nb, nb', u, c]) or
	(c in Photo and upload_photo[nb, nb', u, c])

}

	/**add comment operations**/
pred addComment[nb,nb' : NiceBook, u:User, c:Content,comment: Comment]{
	/**pre-condition**/

	//that user should have permission to add comment according to privacy settings
	u in getUserWhoCanView[nb,hasWallOwner.((nb.hasContent).c)]

	//that content should be in the wall, which means that content is published
	c in nb.contains[hasWallOwner.(nb.hasPeople)]
	comment not in nb.contains[hasWallOwner.(nb.hasPeople)]

	//if c does not in Nicebook upload them
	//if c already uploaded, skip this upload but make sure that 
	// (comment not in nb.hasContent[nb.hasPeople] and upload[nb,nb',u,comment]) or
	// (comment in nb.hasContent[u] and preUploadAndPublish[nb,nb',u,comment] 
	// 	and nb'.hasContent=nb.hasContent and comment not in (nb.contains[hasWallOwner.(nb.hasPeople)]) 

	c in comment.attachedTo

	nb'.hasContent=nb.hasContent+u->comment
	nb'.contains=nb.contains+{w: (nb.contains).c, cm: Comment | cm = comment}

    nb'.hasPeople=nb.hasPeople
    nb'.hasFriends=nb.hasFriends
}

//run addComment for 3

assert addCommentPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content,comment:Comment |
		invariant[nb] and addComment[nb,nb',u,c,comment] implies
		invariant[nb']
}

check addCommentPreserveInvariant for 7

//run upload for 3

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
	all p: c.hasPhotos | p not in nb.contains[(hasWallOwner.u)]
	//note's comment
	// get_comment_from_content[c] not in (hasWallOwner.u).contains
	// note's photo's comment
	// all p: c.hasPhotos |
	// 	get_comment_from_content[p]	not in (hasWallOwner.u).contains

	// remove note and everything belong to it
	nb'.hasContent = nb.hasContent - u->c -
		{user: User, p:Photo | user = u and p in c.hasPhotos}
		// {
		// 	user: User, cm: Comment | user=(nb.hasContent).cm and cm in 
		// 		(get_comment_from_content[c] +
		// 		{pcm: Comment| all p: c.hasPhotos | pcm in get_comment_from_content[p]})
		// }
}

pred remove_photo[nb, nb': NiceBook, u: User, c: Content]{
	//No note contains photo, if there is a note, then you should remove note
	no hasPhotos.c

	
	//Remove all photo's comment
	// get_comment_from_content[c]	not in nb.contains[(hasWallOwner.u)]
	
	//Remove photo and everything belong to it
	nb'.hasContent = nb.hasContent - u->c

}

//Assumption: only remove unpublished thing
pred remove[nb, nb': NiceBook, u: User, c: Content]{
	// pre condition
	// uploaded but not published, user is in NiceBook
	u in nb.hasPeople and u->c in nb.hasContent and
		c not in nb.contains[(hasWallOwner.u)]

	// c is not a comment
	c not in Comment

	// post condition, remove c based on its type
	(c in Note and remove_note[nb, nb', u, c]) or
	(c in Photo and remove_photo[nb, nb', u, c])

	// frame condition
	nb'.hasPeople = nb.hasPeople
	nb'.hasFriends = nb.hasFriends
	nb'.contains=nb.contains
}

//run remove for 5

assert RemovePreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content |
		invariant[nb] and remove[nb,nb',u,c] implies
		invariant[nb']
}

check RemovePreserveInvariant for 7

	/**publish operations**/


pred publish_note[nb,nb':NiceBook, u:User, c:Content, w:Wall]{
   	// photos included in this note should be able to publish
    all p:c.hasPhotos |
		p in nb.hasContent[u] and 
		p not in nb.contains[(hasWallOwner.(nb.hasPeople))]

	nb'.contains=nb.contains+w->c+
		{wall: Wall,p:Photo|wall=w and p in c.hasPhotos}
}

pred publish_photo[nb,nb':NiceBook, u:User, c:Content, w:Wall]{
    // this photo should not be contained by a note
    no hasPhotos.c

	nb'.contains=nb.contains+w->c

}

pred publish[nb,nb' : NiceBook, u:User, c:Content, w:Wall]{

	/**pre-condition**/

    //only wall owner can publish content things on their wall
    w.hasWallOwner in u
	//can't publish comment
	c not in Comment

	//if c does not in Nicebook upload them
	//if c already uploaded, skip this upload but make sure that 
	(c not in nb.hasContent[nb.hasPeople] and upload[nb,nb',u,c]) or
	(c in nb.hasContent[u] and preUploadAndPublish[nb,nb',u,c] 
		and nb'.hasContent=nb.hasContent and c not in (nb.contains[hasWallOwner.(nb.hasPeople)])) 

	/**post-condition**/
	//publish c based on its type
	(c in Note and publish_note[nb, nb', u, c,w]) or
	(c in Photo and publish_photo[nb, nb', u, c,w]) 

    nb'.hasPeople=nb.hasPeople
    nb'.hasFriends=nb.hasFriends
}

/**unpublish operation**/
pred unpublish[nb,nb':NiceBook, u:User,c:Content]{
	//content is already publish, user is in NiceBook

	u in nb.hasPeople 
	
	//Assumption: only content owner can unpublish content
	u->c in nb.hasContent 

	no hasPhotos.c

	c not in Comment

	c in nb.contains[hasWallOwner.u]

	nb'.contains=nb.contains - hasWallOwner.(nb.hasPeople)->c -
		{wall: Wall, p:Photo | wall in hasWallOwner.(nb.hasPeople) and p in c.hasPhotos}-		
		{	
			wall: Wall, cm: nb.hasContent[nb.hasPeople] | wall in hasWallOwner.(nb.hasPeople)
			 and cm in ((*attachedTo).c+(*attachedTo).(c.hasPhotos))
		}

	nb'.hasContent=nb.hasContent -		
		{	
			user: User, cm: nb.hasContent[nb.hasPeople] & Comment | user in nb.hasPeople
			and cm in ((*attachedTo).c+(*attachedTo).(c.hasPhotos))//(c in cm.^attachedTo or c.hasPhotos in cm.^attachedTo)
		}

	// frame condition
	nb'.hasPeople = nb.hasPeople
	nb'.hasFriends = nb.hasFriends
}

//run unpublish for 5

assert UnPublishPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content |
		invariant[nb] and unpublish[nb,nb',u,c] implies
		invariant[nb']
}

check UnPublishPreserveInvariant for 7

/**addTag operation**/
pred addTag[nb,nb':NiceBook, u:User,tag:Tag,c:Content]{
	//Precondition

	//content is already publish, user is in NiceBook
	//Assumption!: only content owner can tag other user 

	u in (nb.hasContent).c and u->c in nb.hasContent and 
	
	c in tag.associatedWith

	//Only user's hasFriends can tag that user
	tag.taggedUser = nb.hasFriends[u]

	//Assumption: You can't tag a photo in a note
	no hasPhotos.c

	c not in Comment

	hasWallOwner.u->c in nb.contains

	hasWallOwner.(tag.taggedUser)->c not in nb.contains

	//end of Precondtion
	nb'.contains=nb.contains+hasWallOwner.(tag.taggedUser)->c+
		{wall: Wall, p:Photo | wall = hasWallOwner.(tag.taggedUser) and p in c.hasPhotos} +
		{
			wall: Wall, cm: nb.hasContent[nb.hasPeople] | wall = hasWallOwner.(tag.taggedUser)
			 and cm in ((*attachedTo).c+(*attachedTo).(c.hasPhotos))
		}

	//frame condition
	nb'.hasContent=nb.hasContent
	nb'.hasFriends=nb.hasFriends
	nb'.hasPeople=nb.hasPeople
}

//run addTag for 3
assert AddTagPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content, tag:Tag |
		invariant[nb] and addTag[nb,nb',u,tag,c] implies
		invariant[nb']
}

/**removeTag operation **/
pred removeTag[nb,nb':NiceBook, u:User, tag:Tag]{
	//Assumption: Only associatedWith.tag's owner can removeTag
	u in (nb.hasContent).(tag.associatedWith)

	u in nb.hasPeople

	//Assumption: You cannot remove a tag from a photo that in a note 
	no hasPhotos.(tag.associatedWith)

	tag.associatedWith in nb.contains[hasWallOwner.(tag.taggedUser)]

	nb'.contains=nb.contains- hasWallOwner.((tag.taggedUser))->(tag.associatedWith) -
		{wall:Wall, p:Photo| wall in hasWallOwner.((tag.taggedUser)) and p in (tag.associatedWith).hasPhotos} -
		{	
			wall: Wall, cm: nb.hasContent[nb.hasPeople] | wall in hasWallOwner.((tag.taggedUser))
			 and cm in ((*attachedTo).(tag.associatedWith)+(*attachedTo).((tag.associatedWith).hasPhotos))
		}

	nb'.hasContent=nb.hasContent
	nb'.hasFriends=nb.hasFriends
	nb'.hasPeople=nb.hasPeople
}

run removeTag for 3

assert RemoveTagPreserveInvariant {
	all nb, nb': NiceBook, u:User, tag:Tag |
		invariant[nb] and removeTag[nb,nb',u,tag] implies
		invariant[nb']
}

check RemoveTagPreserveInvariant for 7

check AddTagPreserveInvariant for 7

run publish for 7

assert PublishPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content, w:Wall |
		invariant[nb] and publish[nb,nb',u,c,w] implies
		invariant[nb']
}

check PublishPreserveInvariant for 7

fun getUserWhoCanView[nb:NiceBook, w: Wall]: set User{
	w.hasPrivacySetting=EveryOne implies {nb.hasPeople} 
	
	else w.hasPrivacySetting=FriendsOfFriends implies {nb.hasFriends[nb.hasFriends[w.hasWallOwner]]+nb.hasFriends[w.hasWallOwner]+w.hasWallOwner} //Default All User

	else w.hasPrivacySetting=Friends implies {nb.hasFriends[w.hasWallOwner]+w.hasWallOwner} //Default All User
	
	else {w.hasWallOwner}
}

fun viewable[nb:NiceBook,u:User]:set Content{
	{c:nb.hasContent[nb.hasPeople]|
		u in getUserWhoCanView[nb,hasWallOwner.((nb.hasContent).c)]
		and (some w:hasWallOwner.(nb.hasPeople)| c in nb.contains[w])}
}

run {
	all nb: NiceBook | invariant[nb]
} for 5 but exactly 1 NiceBook, exactly 4 User, exactly 2 Note, exactly 3 Comment, exactly 2 Photo
