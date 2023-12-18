// The prototype instance for simplicity
sig User {
    name: one String
}

sig Student extends User {
    // A student can choose different teams for different battles in a tournament
    teams: set Team,
    battles: set Battle 
}

sig Instructor extends User {
    // An Instructor can create many tournaments and battles
    tournaments: set Tournament,
    battles: set Battle
}

sig Tournament {
    // every tournament has a single creator and may have assistant instructors
    creator: one Instructor,
    assistants: set Instructor,
    battles: set Battle,
    students: set Student,
    var status: TournamentStatus
}

sig Battle {
    tournament: one Tournament,
    creator: one Instructor,
    assistants: set Instructor,
    kata: set Kata,
    teams: set Team,
    minStudents: one Int,
    maxStudents: one Int,
    registrationDeadline: one DateTime,
    submissionDeadline: one DateTime,
    scoreConfig: one ScoreConfig,
    var status: BattleStatus
}

sig Team {
    students: set Student,
    battle: one Battle,
    score: one Score,
    enrollmentTime: one DateTime
}

sig Score {
    functional: one Int,
    timeliness: one Int,
    quality: one Int,
    personal: lone Int
}

sig Kata {
    description: one String,
    testCases: set TestCase,
    buildScripts: set BuildScript,
    battle: one Battle
}

sig Solution {
  submissionTime: one DateTime,
  team: one Team,
  kata: one Kata,
  score: one Score,
  var status: SolutionStatus
}

// A DateTime signature to represent a point in time
sig DateTime {
  year: one Int,
  month: one Int,
  day: one Int,
  hour: one Int,
  minute: one Int
}

sig TestCase {}
sig BuildScript {}
sig ScoreConfig {}

enum BattleStatus {BatOpen, BatClosed}
enum TournamentStatus {TourOpen, TourClosed}
enum SolutionStatus {Submitted, Evaluated}

// ###################################### PREDICATES ######################################

// Check if a DateTime is before another
pred isBefore[d1, d2: DateTime] {
  d1.year < d2.year or
  (d1.year = d2.year and d1.month < d2.month) or
  (d1.year = d2.year and d1.month = d2.month and d1.day < d2.day) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour < d2.hour) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour = d2.hour and d1.minute < d2.minute)
}

// Close a Battle
pred closeBattle [b: Battle] {
    b.status = BatOpen
    b.status' = BatClosed
}

// Close a Tournament
pred closeTournament [t: Tournament] {
    t.status = TourOpen
    t.status' = TourClosed
}

// ###################################### FACTS ######################################

// A fact to ensure DateTime values are valid
fact validDateTime {
  all dt: DateTime | (dt.year > 0) and 
    (dt.month >= 1 and dt.month <= 12) and
    (dt.day >= 1 and dt.day <= 31) and // it is not completely accurate since months have different number of days, but for easyness of notation we are not accounting for it
    (dt.hour >= 0 and dt.hour <= 23) and
    (dt.minute >= 0 and dt.minute <= 59)
}

// A fact to ensure Score values are valid
fact validScoreValues {
    all sc: Score | sc.functional + sc.timeliness + sc.quality + sc.personal <= 100 and
    sc.functional + sc.timeliness + sc.quality + sc.personal >= 0
}

// Teams can't enroll in a battle after the deadline
fact teamsCantEnrollAfterDeadline {
  all b: Battle, t: Team |
    (t in b.teams) implies isBefore[t.enrollmentTime, b.registrationDeadline]
}

// Students can be in one team in each battle
fact studentInOneTeamPerBattle {
  all s: Student | all disj t1, t2: s.teams | t1.battle != t2.battle
}

// Solutions cannot be submitted after the deadline
fact solutionsCannotBeSubmittedAfterDeadline {
  all s: Solution | isBefore[s.submissionTime, s.kata.battle.submissionDeadline]
}

// Students cannot send solutions to a battle they are not enrolled in
fact studentsCanNotSendSolutionsIfNotEnrolled {
    all s: Solution | s.team in s.kata.battle.teams
}

//The solution time must be after the registration deadline
fact solutionTimeAfterRegistrationDeadline {
    all s: Solution | isBefore[s.kata.battle.registrationDeadline, s.submissionTime]
}

// The number of members of a team should be between the min and max value specified in the battle
fact numberTeamMembers {
    all t: Team | #t.students >= t.battle.minStudents and #t.students <= t.battle.maxStudents
}

// Battle will eventually be closed
fact battleEventuallyClosed {
    all b: Battle | always (b.status = BatOpen implies eventually b.status = BatClosed)
}

// Tournament will eventually be closed
fact tournamentEventuallyClosed {
    all t: Tournament | always (t.status = TourOpen implies eventually t.status = TourClosed)
}

// The Submission deadline cannot be before the registration deadline
fact submissionDeadlineAfterEnrollmentDeadline {
  all b: Battle | isBefore[b.registrationDeadline, b.submissionDeadline]
}

// Battle historically open
fact battleHistoricallyOpen{
    all b: Battle | always (b.status = BatOpen implies historically b.status = BatOpen)
}

// Tournament historically open
fact tournamentHistoricallyOpen {
    all t: Tournament | always (t.status = TourOpen implies historically t.status = TourOpen)
}

// Battle cannot be reopened
fact battleCannotBeReopened {
    all b: Battle | always ( b.status = BatClosed implies after always b.status = BatClosed)
}

// Tournament cannot be reopened
fact tournamentCannotBeReopened {
    all t: Tournament | always ( t.status = TourClosed implies after always t.status = TourClosed)
}

// Kata should have at least one test case
fact allKatasHaveTestCases {
  all k: Kata | some k.testCases
}

// Kata cannot have duplicated test cases
fact noDuplicateTestCasesInKata {
  all k: Kata | all disj tc1, tc2: k.testCases | tc1 != tc2
}

// If a Battle is closed, it must have been closed sometime in the past
fact ifBattleClosedDidClose {
    all b : Battle | always (b.status = BatClosed implies once closeBattle[b] )
}

// If a Tournament is closed, it must have been closed sometime in the past
fact ifTournamentClosedDidClose {
    all t : Tournament | always (t.status = TourClosed implies once closeTournament[t] )
}

// Solution historically submitted
fact solutionHistoricallySubmitted{
    all s: Solution | always (s.status = Submitted implies historically s.status = Submitted)
}

// Solution will eventually be Evaluated
fact solutionEventuallyEvaluated {
    all s: Solution | always (s.status = Submitted implies eventually s.status = Evaluated)
}

// The creator of a tournament cannot be an assistant instructor
fact noAssistantCreator {
    all t: Tournament | t.creator not in t.assistants
}

pred showStudentSubmitsSolution {
  some s: Solution, st: Student, t: Team, b: Battle, k: Kata, currentTime: DateTime |
    st in t.students and
    t in b.teams and
    s.team = t and
    s.kata = k and
    k.battle = b and
    s.status = Submitted and
    isBefore[currentTime, b.submissionDeadline]
}

run showStudentSubmitsSolution for 5

