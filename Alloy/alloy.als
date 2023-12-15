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
    score: one Score
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
  year: Int,
  month: Int,
  day: Int,
  hour: Int,
  minute: Int
}

sig TestCase {}
sig BuildScript {}
sig ScoreConfig {}

fact allProjectsHaveTestCases {
  all p: Project | some p.testCases
}

fact noDuplicateTestCasesInProject {
  all p: Project | all disj tc1, tc2: p.testCases | tc1 != tc2
}

// Students can be in one team in each battle
fact studentInOneTeamPerBattle {
  all s: Student | all disj t1, t2: s.teams | t1.battle != t2.battle
}

// A fact to ensure DateTime values are valid
fact validDateTime {
  all dt: DateTime | 
    dt.year > 0 and
    dt.month in 1..12 and
    dt.day in 1..31 and
    dt.hour in 0..23 and
    dt.minute in 0..59
}

// A predicate to check if a DateTime is before another
pred isBefore[d1, d2: DateTime] {
  d1.year < d2.year or
  (d1.year = d2.year and d1.month < d2.month) or
  (d1.year = d2.year and d1.month = d2.month and d1.day < d2.day) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour < d2.hour) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour = d2.hour and d1.minute < d2.minute)
}

// A fact to ensure students can't enroll in a battle after the deadline
fact studentsCantEnrollAfterDeadline {
  all s: Student, b: Battle, t: Team |
    (s in t.students and t in b.teams) implies isBefore[s.enrollmentTime, b.registrationDeadline]
}

assert checkIsBefore {
  some d1, d2: DateTime | isBefore[d1, d2]
}

// Then you can check this assertion
check checkIsBefore for 5
