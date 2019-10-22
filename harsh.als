sig User{
	addCommentPrivacy: User -> PrivacyLevel,
	otherContentPrivacy: Content -> PrivacyLevel,
	myContentPrivacy: Content -> PrivacyLevel,
	friends: set User,
	upload : some Content
}

sig Wall{
	wallOwner: one User,
	containsContent: set Content
}

abstract sig Content{
	// contentOwner: one User,
	status: set PublishStatus,
	contains : some Content
}

sig Note extends Content{
	//note contains one or more photos
	//notePhotos: set Photo
}

sig Photo extends Content{
	//	photoContains : some Comment
}

sig Comment extends Content{
    //As a comment, I must attach to a piece of content, but that content cannot be itself
	//	commentAttached: set Content
}

sig Tag{
	tagUser: one User,
	tagAssociated: one Content
}

pred contentInvariant[c:Content] {
	one user : User | c in user.upload

	//content cannot contain it self
	c not in c.^contains
}

pred userInvariant[u:User]{
    	//As a user, I must be the friend of my friends
    	// all u':User | u' in u.friends implies u in u'.friends
	all u':u.friends | u in u'.friends
    	//As a user, I cannot be my own friend
   	 u not in u.friends 

	//user has one wall
	one wall : Wall | u in wall.wallOwner
}

pred photoInvariant[p:Photo]{
	//photo cannot contain another photo
	all c : p.contains | c not in Photo

	//photo cannot contain note
	all c : p.contains | c not in Note

	//photo contains 0 or more comments
	//satisfied

	//all note can have 0 or more tags
	//some notes contain 1 or more tags
	some p1 : Photo |some t: Tag | p1 in t.tagAssociated

	//privacy setting to allow who can view it
}


pred noteInvariant[n:Note]{
	//note contains one or more photos
	all c : n.contains | c in Photo

	// all notes must contain one or more photos
	all n1 : Note| some p : Photo | p in n1.contains

	// all notes contain 0 or more comments
	//some nodes contain 1 or more comments
	some n1 : Note|some c : Comment | c in n1.contains

	//notes dont contain notes
	all c : n.contains | c not in Note

	//all note can have 0 or more tags
	//some notes contain 1 or more tags
	some n1 : Note|some t: Tag | n1 in t.tagAssociated

	//privacy setting to allow who can view it
}

pred commentInvariant[c:Comment]{

	// comment cannot contain notes
	all content : c.contains | content not in Note

	// comment cannot contain photos
	all content : c.contains | content not in Photo

	//comment can contain comment
	// already satisfied as content connects to content and we said comment cannot contain note or photo
	
//	c not in c.^commentAttached
//	some content : Content | content not in Comment 
							//	and content in c.^commentAttached
      
	

	 //As a comment, I must attach to a piece of content, but that content cannot be itself
       
	//written in content invariant, pls check
	//c not in c.*commentAttached
      

	 //As a comment, I can only attach to the content of my owner or my owner's friends
	// all comments can be attached to owner or the owner's friend
	//this will come in privacy?

    //	one content: c.commentAttached | one user : content.contentOwner | c.contentOwner in user.friends or c.contentOwner in user
   	//TODO As a comment, I must have a privacy setting that determines who is able to view me 
}

pred tagInvariant[t:Tag]{
	//tag cannot be associated to comment
	lone content : t.tagAssociated | content not in Comment

	//	one t.tagUser	
	//	one t.tagAssociated

    //As a tag, I must associate to a note or a photo
    all comment: Comment| comment not in t.tagAssociated

    //As a tag, I must reference to a user, and that user cannot be my owner
    all user: t.tagUser | user not in upload.(t.tagAssociated)
}

pred wallInvariant[w:Wall]{
	
	//A user can add a comment only to a piece of content that it owns or is visible on another user’s wall.
	// this is done through privacy

	//As a wall, my content must be from my owner or my owner's friends
//	all content: w.containsContent | content.contentOwner in w.wallOwner 
}

pred invariant[]{
    all u:User|userInvariant[u]
    all p:Photo|photoInvariant[p]
    all c:Comment|commentInvariant[c]
    all t:Tag|tagInvariant[t]
	all w:Wall|wallInvariant[w]
} 

//assert CheckAll {
    // all c:Comment|commentInvariant[c]
//	all u:User|userInvariant[u]
//}

//check CheckAll for 3 but exactly 2 User, exactly 0 Photo, exactly 0 Comment
abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, EveryOne extends PrivacyLevel{}

abstract sig PublishStatus{}
one sig Published, Unpublished extends PublishStatus{}

run {
    invariant
}for 5 but exactly 2 User, exactly 2 Photo, exactly 3 Comment
