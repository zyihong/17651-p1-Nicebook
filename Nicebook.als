sig User{
	addCommentPrivacy: User -> PrivacyLevel,
	otherContentPrivacy: Content -> PrivacyLevel,
	myContentPrivacy: Content -> PrivacyLevel,
	friends: User -> set User
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
	commentOwner: one User,
	commentAttached: one Content
}

sig Tag{
	tagUser: one User,
	tagAssociated: one Content
}

abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, EveryOne extends PrivacyLevel{}

abstract sig PublishStatus{}
one sig Published, Unpublished extends PublishStatus{}
