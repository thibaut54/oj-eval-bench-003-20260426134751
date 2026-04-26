// ICPC Management System
// Implements an ICPC contest backend: teams, submissions, scoreboard,
// freeze and scroll operations, and queries.

#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <string>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <memory>

using std::string;
using std::vector;

constexpr int MAX_PROB = 26;
constexpr int STAT_AC = 0;
constexpr int STAT_WA = 1;
constexpr int STAT_RE = 2;
constexpr int STAT_TLE = 3;
constexpr int STAT_ALL = 4;

struct ProblemState {
    bool solved = false;
    int wrong_before_ac = 0;       // X if solved
    int solve_time = 0;            // T if solved
    int wrong_attempts = 0;        // wrong before solving (becomes wrong_before_ac), or total wrong if not solved
    bool frozen = false;
    int frozen_subs_count = 0;     // y in display
    int first_ac_in_freeze = -1;   // -1 if no AC during freeze
    int wrong_in_freeze_before_ac = 0;
};

struct LastSub {
    int problem = 0;
    int status = 0;
    int time = 0;
    bool valid = false;
};

struct Team {
    string name;
    int idx = 0;
    int solved_count = 0;
    int penalty = 0;
    int solve_times[MAX_PROB];          // sorted descending, length = solved_count
    vector<ProblemState> problems;      // size M
    int frozen_problem_count = 0;
    unsigned int frozen_mask = 0;       // bit i set if problem i is frozen
    // last_sub[problem (0..M-1, MAX_PROB=ALL)][status (0..3, STAT_ALL=4)]
    LastSub last_sub[MAX_PROB + 1][5];

    int smallestFrozenProblem() const {
        if (frozen_mask == 0) return -1;
        return __builtin_ctz(frozen_mask);
    }
};

// Strict comparator: a ranks higher than b (returns true if a should come BEFORE b)
static inline bool rankLess(const Team* a, const Team* b) {
    if (a->solved_count != b->solved_count) return a->solved_count > b->solved_count;
    if (a->penalty != b->penalty) return a->penalty < b->penalty;
    int n = a->solved_count;
    for (int i = 0; i < n; ++i) {
        if (a->solve_times[i] != b->solve_times[i]) return a->solve_times[i] < b->solve_times[i];
    }
    return a->name < b->name;
}

static int g_M = 0;
static bool g_started = false;
static bool g_freeze_active = false;
static vector<std::unique_ptr<Team>> g_teams_storage;
static vector<Team*> g_teams;
static std::unordered_map<string, Team*> g_name2team;

// Live ranking maintained as sorted vector. Index 0 is rank 1 (best).
static vector<Team*> g_ranking;
// team_idx -> current position in g_ranking
static vector<int> g_pos_in_ranking;
// Snapshot of ranking at last flush; used for QUERY_RANKING. Indexed by team idx.
static vector<int> g_displayed_rank;

// Output buffer
static constexpr int OBUF_SZ = 1 << 22;
static char g_obuf[OBUF_SZ];
static int g_olen = 0;

inline void out_flush() {
    if (g_olen > 0) {
        fwrite(g_obuf, 1, g_olen, stdout);
        g_olen = 0;
    }
}

inline void out_str(const char* s) {
    while (*s) {
        if (g_olen >= OBUF_SZ) out_flush();
        g_obuf[g_olen++] = *s++;
    }
}

inline void out_str_n(const char* s, int n) {
    while (n > 0) {
        int avail = OBUF_SZ - g_olen;
        if (avail == 0) { out_flush(); avail = OBUF_SZ; }
        int copy = n < avail ? n : avail;
        memcpy(g_obuf + g_olen, s, copy);
        g_olen += copy;
        s += copy;
        n -= copy;
    }
}

inline void out_char(char c) {
    if (g_olen >= OBUF_SZ) out_flush();
    g_obuf[g_olen++] = c;
}

inline void out_int(int x) {
    if (g_olen + 12 > OBUF_SZ) out_flush();
    if (x == 0) { g_obuf[g_olen++] = '0'; return; }
    if (x < 0) { g_obuf[g_olen++] = '-'; x = -x; }
    char buf[12];
    int n = 0;
    while (x > 0) { buf[n++] = (char)('0' + (x % 10)); x /= 10; }
    while (n > 0) g_obuf[g_olen++] = buf[--n];
}

static int statusFromString(const char* s) {
    if (!strcmp(s, "Accepted")) return STAT_AC;
    if (!strcmp(s, "Wrong_Answer")) return STAT_WA;
    if (!strcmp(s, "Runtime_Error")) return STAT_RE;
    if (!strcmp(s, "Time_Limit_Exceed")) return STAT_TLE;
    if (!strcmp(s, "ALL")) return STAT_ALL;
    return -1;
}

static const char* statusToString(int s) {
    switch (s) {
        case STAT_AC:  return "Accepted";
        case STAT_WA:  return "Wrong_Answer";
        case STAT_RE:  return "Runtime_Error";
        case STAT_TLE: return "Time_Limit_Exceed";
        default:       return "?";
    }
}

// Insert time into team's solve_times keeping it sorted descending.
static inline void addSolveTime(Team* t, int time) {
    int n = t->solved_count - 1; // new count assumed already incremented; actual length stored is solved_count - 1 before insert
    // Find insertion index in [0..n] for sorted-desc; smaller indices have larger values.
    int i = n;
    while (i > 0 && t->solve_times[i - 1] < time) {
        t->solve_times[i] = t->solve_times[i - 1];
        --i;
    }
    t->solve_times[i] = time;
}

// Bubble up team t (whose metrics just improved) to its correct position.
static inline void bubbleUp(Team* t) {
    int p = g_pos_in_ranking[t->idx];
    while (p > 0 && rankLess(g_ranking[p], g_ranking[p - 1])) {
        Team* above = g_ranking[p - 1];
        g_ranking[p - 1] = t;
        g_ranking[p] = above;
        g_pos_in_ranking[above->idx] = p;
        --p;
    }
    g_pos_in_ranking[t->idx] = p;
}

// Like bubbleUp but only used during scroll; returns the original position.
// Returns the new position.
static inline int bubbleUpAt(int original_pos) {
    Team* t = g_ranking[original_pos];
    int p = original_pos;
    while (p > 0 && rankLess(g_ranking[p], g_ranking[p - 1])) {
        Team* above = g_ranking[p - 1];
        g_ranking[p - 1] = t;
        g_ranking[p] = above;
        g_pos_in_ranking[above->idx] = p;
        --p;
    }
    g_pos_in_ranking[t->idx] = p;
    return p;
}

static inline void rebuildDisplayedRank() {
    if ((int)g_displayed_rank.size() < (int)g_ranking.size())
        g_displayed_rank.assign(g_ranking.size(), 0);
    for (size_t i = 0; i < g_ranking.size(); ++i) {
        g_displayed_rank[g_ranking[i]->idx] = (int)i;
    }
}

static inline void recordSubmission(Team* t, int p, int s, int time) {
    LastSub sub{p, s, time, true};
    t->last_sub[p][s] = sub;
    t->last_sub[p][STAT_ALL] = sub;
    t->last_sub[MAX_PROB][s] = sub;
    t->last_sub[MAX_PROB][STAT_ALL] = sub;
}

static void doAddTeam(const string& name) {
    if (g_started) {
        out_str("[Error]Add failed: competition has started.\n");
        return;
    }
    if (g_name2team.count(name)) {
        out_str("[Error]Add failed: duplicated team name.\n");
        return;
    }
    auto up = std::unique_ptr<Team>(new Team());
    up->name = name;
    up->idx = (int)g_teams.size();
    Team* p = up.get();
    g_teams_storage.push_back(std::move(up));
    g_teams.push_back(p);
    g_name2team[name] = p;
    out_str("[Info]Add successfully.\n");
}

static void doStart(int /*duration*/, int problemCount) {
    if (g_started) {
        out_str("[Error]Start failed: competition has started.\n");
        return;
    }
    g_started = true;
    g_M = problemCount;
    for (Team* t : g_teams) {
        t->problems.assign(g_M, ProblemState{});
    }
    // Build initial ranking sorted by name (lex order)
    g_ranking = g_teams;
    std::sort(g_ranking.begin(), g_ranking.end(),
              [](Team* a, Team* b){ return a->name < b->name; });
    g_pos_in_ranking.assign(g_teams.size(), 0);
    for (size_t i = 0; i < g_ranking.size(); ++i) {
        g_pos_in_ranking[g_ranking[i]->idx] = (int)i;
    }
    g_displayed_rank.assign(g_teams.size(), 0);
    rebuildDisplayedRank();
    out_str("[Info]Competition starts.\n");
}

static void doSubmit(Team* t, int p, int s, int time) {
    recordSubmission(t, p, s, time);
    auto& ps = t->problems[p];
    if (ps.solved) return;

    if (g_freeze_active) {
        if (!ps.frozen) {
            ps.frozen = true;
            t->frozen_problem_count++;
            t->frozen_mask |= (1u << p);
        }
        ps.frozen_subs_count++;
        if (s == STAT_AC && ps.first_ac_in_freeze == -1) {
            ps.first_ac_in_freeze = time;
            ps.wrong_in_freeze_before_ac = ps.frozen_subs_count - 1;
        }
        return;
    }

    if (s == STAT_AC) {
        ps.solved = true;
        ps.solve_time = time;
        ps.wrong_before_ac = ps.wrong_attempts;
        t->solved_count++;
        t->penalty += 20 * ps.wrong_before_ac + time;
        addSolveTime(t, time);
        bubbleUp(t);
    } else {
        ps.wrong_attempts++;
    }
}

static void unfreezeProblem(Team* t, int p) {
    auto& ps = t->problems[p];
    if (!ps.frozen) return;
    ps.frozen = false;
    t->frozen_problem_count--;
    t->frozen_mask &= ~(1u << p);

    if (ps.first_ac_in_freeze != -1) {
        ps.solved = true;
        ps.solve_time = ps.first_ac_in_freeze;
        ps.wrong_before_ac = ps.wrong_attempts + ps.wrong_in_freeze_before_ac;
        t->solved_count++;
        t->penalty += 20 * ps.wrong_before_ac + ps.solve_time;
        addSolveTime(t, ps.solve_time);
    } else {
        ps.wrong_attempts += ps.frozen_subs_count;
    }
    ps.frozen_subs_count = 0;
    ps.first_ac_in_freeze = -1;
    ps.wrong_in_freeze_before_ac = 0;
}

static void writeCell(const ProblemState& ps) {
    if (ps.frozen) {
        if (ps.wrong_attempts == 0) {
            out_char('0');
        } else {
            out_char('-');
            out_int(ps.wrong_attempts);
        }
        out_char('/');
        out_int(ps.frozen_subs_count);
    } else if (ps.solved) {
        out_char('+');
        if (ps.wrong_before_ac != 0) out_int(ps.wrong_before_ac);
    } else {
        if (ps.wrong_attempts == 0) {
            out_char('.');
        } else {
            out_char('-');
            out_int(ps.wrong_attempts);
        }
    }
}

static void printScoreboard() {
    for (size_t i = 0; i < g_ranking.size(); ++i) {
        Team* t = g_ranking[i];
        out_str_n(t->name.data(), (int)t->name.size());
        out_char(' ');
        out_int((int)i + 1);
        out_char(' ');
        out_int(t->solved_count);
        out_char(' ');
        out_int(t->penalty);
        for (int j = 0; j < g_M; ++j) {
            out_char(' ');
            writeCell(t->problems[j]);
        }
        out_char('\n');
    }
}

static void doFlush() {
    out_str("[Info]Flush scoreboard.\n");
    rebuildDisplayedRank();
}

static void doFreeze() {
    if (g_freeze_active) {
        out_str("[Error]Freeze failed: scoreboard has been frozen.\n");
        return;
    }
    g_freeze_active = true;
    out_str("[Info]Freeze scoreboard.\n");
}

static void doScroll() {
    if (!g_freeze_active) {
        out_str("[Error]Scroll failed: scoreboard has not been frozen.\n");
        return;
    }
    out_str("[Info]Scroll scoreboard.\n");
    // Implicit flush: snapshot displayed ranks
    rebuildDisplayedRank();
    printScoreboard();

    int n = (int)g_ranking.size();
    int i = n - 1;
    while (i >= 0) {
        Team* T = g_ranking[i];
        if (T->frozen_problem_count == 0) {
            --i;
            continue;
        }
        int p = T->smallestFrozenProblem();
        unfreezeProblem(T, p);
        // Bubble T up if AC during freeze improved its rank
        int new_i = bubbleUpAt(i);
        if (new_i < i) {
            // Output: T moved from i to new_i, the team currently at new_i+1 was the displaced one
            Team* team2 = g_ranking[new_i + 1];
            out_str_n(T->name.data(), (int)T->name.size());
            out_char(' ');
            out_str_n(team2->name.data(), (int)team2->name.size());
            out_char(' ');
            out_int(T->solved_count);
            out_char(' ');
            out_int(T->penalty);
            out_char('\n');
        }
        // i unchanged: ranking[i] may now be a different team
    }

    g_freeze_active = false;
    rebuildDisplayedRank();
    printScoreboard();
}

static void queryRanking(const string& name) {
    auto it = g_name2team.find(name);
    if (it == g_name2team.end()) {
        out_str("[Error]Query ranking failed: cannot find the team.\n");
        return;
    }
    Team* t = it->second;
    out_str("[Info]Complete query ranking.\n");
    if (g_freeze_active) {
        out_str("[Warning]Scoreboard is frozen. The ranking may be inaccurate until it were scrolled.\n");
    }
    out_str_n(t->name.data(), (int)t->name.size());
    out_str(" NOW AT RANKING ");
    out_int(g_displayed_rank[t->idx] + 1);
    out_char('\n');
}

static void querySubmission(const string& name, const char* probStr, const char* statStr) {
    auto it = g_name2team.find(name);
    if (it == g_name2team.end()) {
        out_str("[Error]Query submission failed: cannot find the team.\n");
        return;
    }
    out_str("[Info]Complete query submission.\n");
    Team* t = it->second;
    int p = (!strcmp(probStr, "ALL")) ? MAX_PROB : (probStr[0] - 'A');
    int s = statusFromString(statStr);
    LastSub& ls = t->last_sub[p][s];
    if (!ls.valid) {
        out_str("Cannot find any submission.\n");
        return;
    }
    out_str_n(t->name.data(), (int)t->name.size());
    out_char(' ');
    out_char((char)('A' + ls.problem));
    out_char(' ');
    out_str(statusToString(ls.status));
    out_char(' ');
    out_int(ls.time);
    out_char('\n');
}

// ---------- Input parsing ----------

static inline const char* skipSp(const char* p) {
    while (*p == ' ' || *p == '\t') ++p;
    return p;
}

static inline const char* readTok(const char* p, char* out, int outSize) {
    p = skipSp(p);
    int n = 0;
    while (*p && *p != ' ' && *p != '\t' && *p != '\n' && *p != '\r') {
        if (n + 1 < outSize) out[n++] = *p;
        ++p;
    }
    out[n] = 0;
    return p;
}

static inline const char* readInt(const char* p, int* val) {
    p = skipSp(p);
    int v = 0;
    bool neg = false;
    if (*p == '-') { neg = true; ++p; }
    while (*p >= '0' && *p <= '9') { v = v * 10 + (*p - '0'); ++p; }
    *val = neg ? -v : v;
    return p;
}

static inline const char* readUntilSpaceOrEq(const char* p, char* out, int outSize) {
    p = skipSp(p);
    int n = 0;
    while (*p && *p != ' ' && *p != '\t' && *p != '\n' && *p != '\r' && *p != '=') {
        if (n + 1 < outSize) out[n++] = *p;
        ++p;
    }
    out[n] = 0;
    return p;
}

static inline const char* readKVValue(const char* p, char* out, int outSize) {
    p = skipSp(p);
    if (*p == '=') ++p;
    int n = 0;
    while (*p && *p != ' ' && *p != '\t' && *p != '\n' && *p != '\r') {
        if (n + 1 < outSize) out[n++] = *p;
        ++p;
    }
    out[n] = 0;
    return p;
}

int main() {
    static char line[2048];
    while (fgets(line, sizeof(line), stdin)) {
        size_t L = strlen(line);
        while (L > 0 && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        if (L == 0) continue;

        const char* p = line;
        char cmd[24];
        p = readTok(p, cmd, sizeof(cmd));

        if (!strcmp(cmd, "SUBMIT")) {
            char probStr[8], teamName[32], statusStr[24];
            int t;
            char tmp[8];
            p = readTok(p, probStr, sizeof(probStr));        // problem
            p = readTok(p, tmp, sizeof(tmp));                // BY
            p = readTok(p, teamName, sizeof(teamName));      // team
            p = readTok(p, tmp, sizeof(tmp));                // WITH
            p = readTok(p, statusStr, sizeof(statusStr));    // status
            p = readTok(p, tmp, sizeof(tmp));                // AT
            p = readInt(p, &t);
            int prob = probStr[0] - 'A';
            int s = statusFromString(statusStr);
            auto it = g_name2team.find(teamName);
            if (it != g_name2team.end()) {
                doSubmit(it->second, prob, s, t);
            }
        } else if (!strcmp(cmd, "FLUSH")) {
            doFlush();
        } else if (!strcmp(cmd, "FREEZE")) {
            doFreeze();
        } else if (!strcmp(cmd, "SCROLL")) {
            doScroll();
        } else if (!strcmp(cmd, "ADDTEAM")) {
            char name[32];
            p = readTok(p, name, sizeof(name));
            doAddTeam(name);
        } else if (!strcmp(cmd, "QUERY_RANKING")) {
            char name[32];
            p = readTok(p, name, sizeof(name));
            queryRanking(name);
        } else if (!strcmp(cmd, "QUERY_SUBMISSION")) {
            char name[32], prob[16], status[24];
            char tmp[16];
            p = readTok(p, name, sizeof(name));
            p = readTok(p, tmp, sizeof(tmp));                // WHERE
            p = readUntilSpaceOrEq(p, tmp, sizeof(tmp));     // PROBLEM
            p = readKVValue(p, prob, sizeof(prob));
            p = readTok(p, tmp, sizeof(tmp));                // AND
            p = readUntilSpaceOrEq(p, tmp, sizeof(tmp));     // STATUS
            p = readKVValue(p, status, sizeof(status));
            querySubmission(name, prob, status);
        } else if (!strcmp(cmd, "START")) {
            char tmp[16];
            int d, pc;
            p = readTok(p, tmp, sizeof(tmp));   // DURATION
            p = readInt(p, &d);
            p = readTok(p, tmp, sizeof(tmp));   // PROBLEM
            p = readInt(p, &pc);
            doStart(d, pc);
        } else if (!strcmp(cmd, "END")) {
            out_str("[Info]Competition ends.\n");
            break;
        }
    }
    out_flush();
    return 0;
}
