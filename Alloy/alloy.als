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
    students: set Student
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
    scoreConfig: one ScoreConfig
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
    project: one Project
}

sig Project {
    testCases: set TestCase,
    buildScripts: set BuildScript
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

// ###################################### FACTS ####################################
// A fact to ensure DateTime values are valid
fact validDateTime {
  all dt: DateTime | (dt.year > 0) and 
    (dt.month >= 1 and dt.month <= 12) and
    (dt.day >= 1 and dt.day <= 31) and // it is not completely accurate since months have different number of days, but for easyness of notation we are not accounting for it
    (dt.hour >= 0 and dt.hour <= 23) and
    (dt.minute >= 0 and dt.minute <= 59)
}

// A predicate to check if a DateTime is before another
pred isBefore[d1, d2: DateTime] {
  d1.year < d2.year or
  (d1.year = d2.year and d1.month < d2.month) or
  (d1.year = d2.year and d1.month = d2.month and d1.day < d2.day) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour < d2.hour) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour = d2.hour and d1.minute < d2.minute)
}

// teams can't enroll in a battle after the deadline
fact TeamsCantEnrollAfterDeadline {
  all b: Battle, t: Team |
    (t in b.teams) implies isBefore[t.enrollmentTime, b.registrationDeadline]
}

// Students can be in one team in each battle
fact studentInOneTeamPerBattle {
  all s: Student | all disj t1, t2: s.teams | t1.battle != t2.battle
}

// solutions can not be submitted after the deadline

// students can't send solutions to a battle they are not enrolled in

// instructors can't close a tournament that is already closed

// instructors can't close a battle that is already closed



fact allProjectsHaveTestCases {
  all p: Project | some p.testCases
}

fact noDuplicateTestCasesInProject {
  all p: Project | all disj tc1, tc2: p.testCases | tc1 != tc2
}