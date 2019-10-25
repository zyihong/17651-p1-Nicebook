sig NiceBook{
	hasContent: User-> set Content,
	hasFriends: User -> set User,
	hasPeople: set User,
	contains: Wall-> set Content
}

sig User{
}

sig Wall{
	hasWallOwner: one User,
	hasPrivacySetting: one PrivacyLevel,
}

abstract sig Content{
}

sig Note extends Content{
	hasPhotos: set Photo
}

sig Photo extends Content{}

sig Comment extends Content{
	// A comment must attach to a piece of content, 
	// but that content cannot be itself
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

	// Symmetric friendship
	all u, u' : User | u -> u' in nb.hasFriends implies u' -> u in nb.hasFriends

	// User is not friend of himself
	no u: User | u -> u in nb.hasFriends

	// Nicebook only contains contents owned by users in it
	all u : User | u not in nb.hasPeople implies no nb.hasContent[u]
}

/**Assumption**/
// If the content(note/photo) is unpublished, then it can not contains comments
pred contentInvariant[nb: NiceBook]{
	// No two users can have the same content
	all u, u' : nb.hasPeople, c: Content | 
		u -> c in nb.hasContent and 
		u' -> c in nb.hasContent implies
			u' = u

	// A piece of content (note/photo) can not appear on others wall
	// if it is not on its owner's wall.
	// However, we do not consider comment here because user A can comment
	// on user B's comtent and that will only appear on B's wall
	all c : nb.hasContent[nb.hasPeople] |
		c not in Comment and c not in nb.contains[(hasWallOwner.((nb.hasContent).c))] implies 
		((all w: hasWallOwner.(nb.hasPeople) | c not in nb.contains[w]))
}

pred photoInvariant[nb: NiceBook]{
	// A photo can not be contained by 2 different notes
	 all p :  Photo | 
		all n, n':  Note | 
			p in n.hasPhotos and p in n'.hasPhotos implies n = n'

	// Every note that contains a photo (in content) should be in the
	// hasContent relation in Nicebook
	all p: nb.hasContent[nb.hasPeople] & Photo |
		hasPhotos.p in nb.hasContent[nb.hasPeople]
}

pred noteInvariant[nb : NiceBook]{
	// The owner of the note and the photo it contains should be the same
	all n : nb.hasContent[nb.hasPeople] & Note, u: nb.hasPeople |
		u -> n in nb.hasContent implies
			(all p : n.hasPhotos | u -> p in nb.hasContent)
}

pred commentInvariant[nb: NiceBook]{
	// A comment can not be attached to itself and no cycles should be present
	all c': Comment | c' not in c'.^attachedTo
    
    // A comment can only attach to the content of its owner or be visible on others wall
	all c: nb.hasContent[nb.hasPeople] & Comment |
		c.attachedTo in nb.hasContent[nb.hasPeople]
		
	// TODO:
	all c:  nb.hasContent[nb.hasPeople] & Comment | 
		c in nb.contains[hasWallOwner.(nb.hasPeople)]

	// If a comment is present in the current Nicebook, the content it is attached to 
	// should also be in the Nicebook
 	all c: nb.contains[hasWallOwner.(nb.hasPeople)] & Comment | 
	nb.contains.(c.attachedTo)->c in nb.contains
}

pred tagInvariant[nb: NiceBook]{
    // A tag must associate to a note or a photo
    all comment: Comment, t:Tag| comment not in t.associatedWith

    // A tag must refer to a user, and that user must be the tag's owner's friends
    all t: Tag, u: nb.hasPeople | 
	u = t.taggedUser and t.associatedWith in nb.hasContent[nb.hasPeople] implies 
		u in nb.hasFriends[nb.hasContent.(t.associatedWith)]

	/**Assumption**/	
	// No duplicate tag !
    all t, t':  associatedWith.(nb.hasContent[nb.hasPeople]) |
	t'.taggedUser = t.taggedUser and
	t'.associatedWith = t.associatedWith implies
		t' = t
}

pred wallInvariant[nb: NiceBook]{
	// User has only one wall
 	all u: nb.hasPeople | one hasWallOwner.u
	
	// Everything on the wall in the Nicebook should be in the map of User->Content
	// A wall's content must be from its owner or its owner's friends
	all u: nb.hasPeople | 
		all c: nb.contains[(hasWallOwner.u)] |
			c in User.(nb.hasContent) and
			(c not in Comment implies 
				((nb.hasContent).c = u or (nb.hasContent).c in nb.hasFriends[u]))

	// Everything that attached to/contained by the wall
	// should be contained in the wall
	all w: hasWallOwner.(nb.hasPeople) |
		all c : nb.contains[w] | 
			all content: c.hasPhotos + hasPhotos.c + c.(*attachedTo) | 
				content in nb.contains[w] 
}

pred NoPrivacyViolation[nb: NiceBook]{
	// Just consider everything inside NiceBook,
	// anything else might be in the next state of nb or 
	// they might just be some rubbish but we do not care
    nicebookInvariant[nb]
    contentInvariant[nb]
    photoInvariant[nb]
    noteInvariant[nb]
    commentInvariant[nb]
    tagInvariant[nb]
    wallInvariant[nb]
} 

/** Operations **/
pred preUploadAndPublish[nb,nb':NiceBook,u:User, c:Content]{

	// Pre-condition
	// User is in NiceBook
	u in nb.hasPeople

    // No tag associated to that content
    no associatedWith.c 
	no associatedWith.(c.hasPhotos)

	// Frame condition
	nb'.hasPeople = nb.hasPeople
	nb'.hasFriends = nb.hasFriends
}

/**upload operations**/
pred upload_note[nb, nb': NiceBook, u: User, c: Content]{
	// Photos included in this note should be able to upload
	all p: c.hasPhotos |
		p not in nb.hasContent[nb.hasPeople]

	nb'.hasContent = nb.hasContent + u->c + 
		{user: User, p:Photo|user=u and p in c.hasPhotos}
}

pred upload_photo[nb, nb': NiceBook, u: User, c: Content]{
	// Photo should not be contained by a note
	no hasPhotos.c
	nb'.hasContent = nb.hasContent + u->c
}

// ***Assumption: Comments cannot be uploaded ***/

pred upload[nb, nb': NiceBook, u: User, c: Content]{
	// Assume one can only upload content that is the highest level
	// e.g. if you want to upload a photo that is contained by a note
	// in this case, you should upload the note

	// Pre-condition & frame condtion
    
    // Content not in NiceBook
	c not in nb.hasContent[nb.hasPeople]

	c not in Comment

    preUploadAndPublish[nb,nb',u,c]

	nb'.contains=nb.contains
	// Post-condition
	// Add content based on its type
	(c in Note and upload_note[nb, nb', u, c]) or
	(c in Photo and upload_photo[nb, nb', u, c])

}

/**add comment operations**/
pred addComment[nb,nb' : NiceBook, u:User, c:Content,comment: Comment]{
	// Pre-condition
	// User should have permission to add comment according to privacy settings
	u in getUserWhoCanView[nb,hasWallOwner.((nb.hasContent).c)]

	// Content should be in the wall, which means that content is published
	c in nb.contains[hasWallOwner.(nb.hasPeople)]
	comment not in nb.contains[hasWallOwner.(nb.hasPeople)]

	c in comment.attachedTo

	nb'.hasContent=nb.hasContent+u->comment
	nb'.contains=nb.contains+{w: (nb.contains).c, cm: Comment | cm = comment}

    nb'.hasPeople=nb.hasPeople
    nb'.hasFriends=nb.hasFriends
}

assert addCommentPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content,comment:Comment |
		NoPrivacyViolation[nb] and addComment[nb,nb',u,c,comment] implies
		NoPrivacyViolation[nb']
}

check addCommentPreserveInvariant for 7

assert UploadPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content |
		NoPrivacyViolation[nb] and upload[nb,nb',u,c] implies
		NoPrivacyViolation[nb']
}

check UploadPreserveInvariant for 7

/**remove operations**/
pred remove_note[nb, nb': NiceBook, u: User, c: Content]{
	// Everything belong to this note is unpublished
	// Note's photo
	all p: c.hasPhotos | p not in nb.contains[(hasWallOwner.u)]

	// Remove note and everything belongs to it
	nb'.hasContent = nb.hasContent - u->c -
		{user: User, p:Photo | user = u and p in c.hasPhotos}
}

pred remove_photo[nb, nb': NiceBook, u: User, c: Content]{
	// No note contains photo, if there is a note, then you should remove note
	no hasPhotos.c
	
	// Remove photo and everything belongs to it
	nb'.hasContent = nb.hasContent - u->c
}

// Assumption: only unpublished contents can be removed
pred remove[nb, nb': NiceBook, u: User, c: Content]{
	// Pre-condition
	// Uploaded but not published, user is in NiceBook
	u in nb.hasPeople and u->c in nb.hasContent and
		c not in nb.contains[(hasWallOwner.u)]

	// Not a comment
	c not in Comment

	// Post-condition
	// Remove c based on its type
	(c in Note and remove_note[nb, nb', u, c]) or
	(c in Photo and remove_photo[nb, nb', u, c])

	// Frame condition
	nb'.hasPeople = nb.hasPeople
	nb'.hasFriends = nb.hasFriends
	nb'.contains=nb.contains
}

assert RemovePreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content |
		NoPrivacyViolation[nb] and remove[nb,nb',u,c] implies
		NoPrivacyViolation[nb']
}

check RemovePreserveInvariant for 7

/**publish operations**/
pred publish_note[nb,nb':NiceBook, u:User, c:Content, w:Wall]{
   	// Photos included in this note should be able to publish
    all p:c.hasPhotos |
		p in nb.hasContent[u] and 
		p not in nb.contains[(hasWallOwner.(nb.hasPeople))]

	nb'.contains=nb.contains+w->c+
		{wall: Wall,p:Photo|wall=w and p in c.hasPhotos}
}

pred publish_photo[nb,nb':NiceBook, u:User, c:Content, w:Wall]{
    // The photo should not be contained by a note
    no hasPhotos.c

	nb'.contains=nb.contains+w->c

}

pred publish[nb,nb' : NiceBook, u:User, c:Content, w:Wall]{
	// Pre-condition
    // Only wall owner can publish content things on their wall
    w.hasWallOwner in u
	
	// Can't publish comment here, use addCommemt instead
	c not in Comment

	// If content does not in Nicebook, upload it
	// If content has already been uploaded, skip this upload
	(c not in nb.hasContent[nb.hasPeople] and upload[nb,nb',u,c]) or
	(c in nb.hasContent[u] and preUploadAndPublish[nb,nb',u,c] 
		and nb'.hasContent=nb.hasContent and c not in (nb.contains[hasWallOwner.(nb.hasPeople)])) 

	// Post-condition
	// Publish content based on its type
	(c in Note and publish_note[nb, nb', u, c,w]) or
	(c in Photo and publish_photo[nb, nb', u, c,w]) 

    nb'.hasPeople=nb.hasPeople
    nb'.hasFriends=nb.hasFriends
}

/**unpublish operation**/
pred unpublish[nb,nb':NiceBook, u:User, c:Content]{
	// Pre-condition
	// User of the content is in NiceBook
	u in nb.hasPeople 
	
	/**Assumption**/
	// Only the content's owner can unpublish the content
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

	// Frame condition
	nb'.hasPeople = nb.hasPeople
	nb'.hasFriends = nb.hasFriends
}

assert UnPublishPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content |
		NoPrivacyViolation[nb] and unpublish[nb,nb',u,c] implies
		NoPrivacyViolation[nb']
}

check UnPublishPreserveInvariant for 7

/**addTag operation**/
pred addTag[nb,nb':NiceBook, u:User,tag:Tag,c:Content]{
	// Pre-condition

	/**Assumption**/
	// A tag can only be attached to published content
	// Only content owner can tag other users
	u in (nb.hasContent).c and u->c in nb.hasContent and 
	
	c in tag.associatedWith

	// Only user's friends can tag that user
	tag.taggedUser = nb.hasFriends[u]

	/**Assumption**/
	// Photos in note cannot be tagged
	no hasPhotos.c

	c not in Comment

	hasWallOwner.u->c in nb.contains

	hasWallOwner.(tag.taggedUser)->c not in nb.contains

	// End of Precondtion
	nb'.contains=nb.contains+hasWallOwner.(tag.taggedUser)->c+
		{wall: Wall, p:Photo | wall = hasWallOwner.(tag.taggedUser) and p in c.hasPhotos} +
		{
			wall: Wall, cm: nb.hasContent[nb.hasPeople] | wall = hasWallOwner.(tag.taggedUser)
			 and cm in ((*attachedTo).c+(*attachedTo).(c.hasPhotos))
		}

	// Frame condition
	nb'.hasContent=nb.hasContent
	nb'.hasFriends=nb.hasFriends
	nb'.hasPeople=nb.hasPeople
}

assert AddTagPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content, tag:Tag |
		NoPrivacyViolation[nb] and addTag[nb,nb',u,tag,c] implies
		NoPrivacyViolation[nb']
}

/**removeTag operation **/
pred removeTag[nb,nb':NiceBook, u:User, tag:Tag]{
	/**Assumption**/
	// Only the owner of the content can remove a tag on the content
	u in (nb.hasContent).(tag.associatedWith)

	u in nb.hasPeople

	/**Assumption**/
	// Tags from photos in notes cannot be removed
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
		NoPrivacyViolation[nb] and removeTag[nb,nb',u,tag] implies
		NoPrivacyViolation[nb']
}

check RemoveTagPreserveInvariant for 7

check AddTagPreserveInvariant for 7

run publish for 7

assert PublishPreserveInvariant {
	all nb, nb': NiceBook, u:User, c:Content, w:Wall |
		NoPrivacyViolation[nb] and publish[nb,nb',u,c,w] implies
		NoPrivacyViolation[nb']
}

check PublishPreserveInvariant for 7

// Get all user that can view the content according to the privacy setting of the wall
fun getUserWhoCanView[nb:NiceBook, w: Wall]: set User{
	w.hasPrivacySetting=EveryOne implies {nb.hasPeople} 
	
	else w.hasPrivacySetting=FriendsOfFriends implies {nb.hasFriends[nb.hasFriends[w.hasWallOwner]]+nb.hasFriends[w.hasWallOwner]+w.hasWallOwner} //Default All User

	else w.hasPrivacySetting=Friends implies {nb.hasFriends[w.hasWallOwner]+w.hasWallOwner} //Default All User
	
	else {w.hasWallOwner}
}

// All content that can be viewed by the user
fun viewable[nb: NiceBook, u: User]: set Content{
	{c:nb.hasContent[nb.hasPeople]|
		u in getUserWhoCanView[nb,hasWallOwner.((nb.hasContent).c)]
		and (some w:hasWallOwner.(nb.hasPeople)| c in nb.contains[w])}
}

run {
	all nb: NiceBook | NoPrivacyViolation[nb]
} for 5 but exactly 1 NiceBook, exactly 4 User, exactly 2 Note, exactly 3 Comment, exactly 2 Photo
