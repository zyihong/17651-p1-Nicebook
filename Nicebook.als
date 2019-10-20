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
	status: one PublishStatus
}

sig Note extends Content{
	notePhotos: set Photo
}

sig Photo extends Content{}

sig Comment extends Content{
    //As a comment, I must attach to a piece of content, but that content cannot be itself
	commentAttached: set Content
}

sig Tag{
	tagUser: one User,
	tagAssociated: one Content
}

pred userInvariant[u:User]{
    //As a user, I must be the friend of my friends
    all u':User | u' in u.friends implies u in u'.friends
    //As a user, I cannot be my own friend
    u not in u.friends 
}

pred photoInvariant[p:Photo]{

}

pred commentInvariant[c:Comment]{
    //As a comment, I must attach to a piece of content, but that content cannot be itself
    c not in c.*commentAttached
    //As a comment, I can only attach to the content of my owner or my owner's friends
    // one content: c.commentAttached | one user : content.contentOwner | c.contentOwner in user.friends or c.contentOwner in user
    //TODO As a comment, I must have a privacy setting that determines who is able to view me 
}

pred tagInvariant[t:Tag]{
    //As a tag, I must associate to a note or a photo
    all comment: Comment| comment not in t.tagAssociated

    //As a tag, I must reference to a user, and that user cannot be my owner
    all user: t.tagUser | user not in t.tagAssociated.contentOwner
}

pred invariant[]{
    all u:User|userInvariant[u]
    all p:Photo|photoInvariant[p]
    all c:Comment|commentInvariant[c]
    all t:Tag|tagInvariant[t]
} 

assert CheckAll {
    all c:Comment|commentInvariant[c]
}

check CheckAll for 5 but exactly 2 User, exactly 2 Photo, exactly 3 Comment
abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, EveryOne extends PrivacyLevel{}

abstract sig PublishStatus{}
one sig Published, Unpublished extends PublishStatus{}

run {
    invariant
}for 5 but exactly 2 User, exactly 2 Photo, exactly 3 Comment