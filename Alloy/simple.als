sig DateTime {
  year: one Int,
  month: one Int,
  day: one Int,
  hour: one Int,
  minute: one Int
}

sig Student {
  solutions: set Solution,
  team: one Team
}

sig Battle {
  submissionDeadline: one DateTime,
  katas: set Kata,
  teams: set Team,
}

sig Team {
  students: set Student,
  battle: one Battle,
  solutions: set Solution
}

sig Kata {
  battle: one Battle,
  solutions: set Solution
}

sig Solution {
  submissionTime: one DateTime,
  team: one Team,
  kata: one Kata,
  student: one Student,
  status: one Status
}

enum Status {
  Submitted, Evaluated, Rejected
}

pred isBefore[d1, d2: DateTime] {
  d1.year < d2.year or
  (d1.year = d2.year and d1.month < d2.month) or
  (d1.year = d2.year and d1.month = d2.month and d1.day < d2.day) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour < d2.hour) or
  (d1.year = d2.year and d1.month = d2.month and d1.day = d2.day and d1.hour = d2.hour and d1.minute < d2.minute)
}

pred submitSolution[s: Solution, currentTime: DateTime] {
  s.submissionTime = currentTime and
  isBefore[s.submissionTime, s.team.battle.submissionDeadline] and
  s.kata in s.team.battle.katas and
  some st: Student | st in s.team.students and s in st.solutions and
  s.status = Submitted
}

fact teamHasStudent {
  all t: Team | some t.students
}

fact solutionForBattleKata {
  all s: Solution | s.kata in s.team.battle.katas
}

fact solutionByTeamStudent {
  all s: Solution | some st: Student | st in s.team.students and s in st.solutions
}

fact solutionBeforeDeadline {
  all s: Solution | isBefore[s.submissionTime, s.team.battle.submissionDeadline]
}

fact solutionSubmittedNotEvaluated {
  all s: Solution | s.status = Submitted implies not (s.status = Evaluated)
}

run submitSolution for 4 but 3 DateTime