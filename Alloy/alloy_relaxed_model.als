// The prototype instance for simplicity
sig User {
    //name: one String
}

sig Student extends User {}

sig Instructor extends User {}

sig Tournament {
    // every tournament has a single creator and may have assistant instructors
    creator: one Instructor,
    assistants: set Instructor,
    battles: some Battle
}

sig Battle {
    tournament: one Tournament,
    katas: some Kata,
    teams: some Team,
    minStudents: one Int,
    maxStudents: one Int,
    registrationDeadline: one DateTime,
    submissionDeadline: one DateTime
}

sig Team {
    students: some Student,
    enrollmentTime: one DateTime
}

sig Score{
    score: one Int
}

sig Kata {
}

sig Solution {
  submissionTime: one DateTime,
  team: one Team,
  kata: one Kata,
  score: one Score
}

// A DateTime signature to represent a point in time
sig DateTime {
  time: one Int
}
// ###################################### PREDICATES ######################################

pred isBefore[d1, d2: DateTime]{
    d1.time < d2.time
}

// ###################################### FACTS ######################################

// A fact to ensure DateTime values are valid
fact validDateTime {
   all dt: DateTime | (dt.time > 0)
}

// A fact to ensure Score values are valid
fact validScoreValues {
    all sc: Score | sc.score <= 5 and
    sc.score >= 0
}

// Teams can't enroll in a battle after the deadline
fact teamsCantEnrollAfterDeadline {
  all b: Battle, t: Team |
    (t in b.teams) implies isBefore[t.enrollmentTime, b.registrationDeadline]
}


// Students can be in one team in each battle
fact studentInOneTeamPerBattle {
  all s: Student, b: Battle, disj t1, t2: b.teams | s in t1.students implies not s in t2.students
}

// Solutions cannot be submitted after the deadline
fact solutionsCannotBeSubmittedAfterDeadline {
  all s: Solution, b: Battle | s.kata in b.katas and isBefore[s.submissionTime, b.submissionDeadline]
}


// Students cannot send solutions to a battle they are not enrolled in
fact studentsCanNotSendSolutionsIfNotEnrolled {
    all s: Solution, b:Battle | s.kata in b.katas and s.team in b.teams
}

//The solution time must be after the registration deadline
fact solutionTimeAfterRegistrationDeadline {
    all s: Solution, b: Battle | s.kata in b.katas and isBefore[b.registrationDeadline, s.submissionTime]
}

// The number of members of a team should be between the min and max value specified in the battle
fact numberTeamMembers {
    all t: Team, b:Battle | t in b.teams and #t.students >= b.minStudents and #t.students <= b.maxStudents
}

// The Submission deadline cannot be before the registration deadline
fact submissionDeadlineAfterEnrollmentDeadline {
  all b: Battle | isBefore[b.registrationDeadline, b.submissionDeadline]
}

// The creator of a tournament cannot be an assistant instructor
fact noAssistantCreator {
    all t: Tournament | t.creator not in t.assistants
}

pred show{
    #Battle = 1 and
    #Tournament = 1 and
    #Kata = 5 and
    #Team = 2 and
    #Solution = 2 and
    #Student = 6
}

run show for 10 but exactly 1 Tournament, 5 Kata, 2 Team, 2 Solution, 6 Student, 1 Battle