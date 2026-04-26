// ICPC Management System
// Implements an ICPC contest backend: teams, submissions, scoreboard,
// freeze and scroll operations, and queries.

#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <string>
#include <vector>
#include <set>
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
    int wrong_before_ac = 0;
    int solve_time = 0;
    int wrong_attempts = 0;
    bool frozen = false;
    int frozen_subs_count = 0;
    int first_ac_in_freeze = -1;
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
    int solve_times[MAX_PROB];
    vector<ProblemState> problems;
    int frozen_problem_count = 0;
    unsigned int frozen_mask = 0;
    LastSub last_sub[MAX_PROB + 1][5];

    int smallestFrozenProblem() const {
        if (frozen_mask == 0) return -1;
        return __builtin_ctz(frozen_mask);
    }
};

struct TeamCmp {
    bool operator()(const Team* a, const Team* b) const {
        if (a->solved_count != b->solved_count) return a->solved_count > b->solved_count;
        if (a->penalty != b->penalty) return a->penalty < b->penalty;
        int n = a->solved_count;
        for (int i = 0; i < n; ++i) {
            if (a->solve_times[i] != b->solve_times[i]) return a->solve_times[i] < b->solve_times[i];
        }
        return a->name < b->name;
    }
};

static int g_M = 0;
static bool g_started = false;
static bool g_freeze_active = false;
static vector<std::unique_ptr<Team>> g_teams_storage;
static vector<Team*> g_teams;
static std::unordered_map<string, Team*> g_name2team;

// Live ranking: sorted by TeamCmp. Begin = best rank.
static std::set<Team*, TeamCmp> g_live;
// Teams with at least one frozen problem (subset of g_live).
static std::set<Team*, TeamCmp> g_frozen_teams;
// Snapshot rank from last flush, indexed by team idx.
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

// Insert time into solve_times keeping descending order; assumes solved_count
// already incremented and the slot at [solved_count - 1] is unwritten.
static inline void addSolveTime(Team* t, int time) {
    int i = t->solved_count - 1;
    while (i > 0 && t->solve_times[i - 1] < time) {
        t->solve_times[i] = t->solve_times[i - 1];
        --i;
    }
    t->solve_times[i] = time;
}

static inline void rebuildDisplayedRank() {
    if ((int)g_displayed_rank.size() < (int)g_teams.size())
        g_displayed_rank.assign(g_teams.size(), 0);
    int r = 0;
    for (Team* t : g_live) {
        g_displayed_rank[t->idx] = r++;
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
        g_live.insert(t);
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
        bool was_frozen_team = (t->frozen_problem_count > 0);
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
        if (!was_frozen_team && t->frozen_problem_count > 0) {
            g_frozen_teams.insert(t);
        }
        return;
    }

    if (s == STAT_AC) {
        g_live.erase(t);
        ps.solved = true;
        ps.solve_time = time;
        ps.wrong_before_ac = ps.wrong_attempts;
        t->solved_count++;
        t->penalty += 20 * ps.wrong_before_ac + time;
        addSolveTime(t, time);
        g_live.insert(t);
    } else {
        ps.wrong_attempts++;
    }
}

static void unfreezeProblemNoRankChange(Team* t, int p) {
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

static void printScoreboardFromLive() {
    int rank = 1;
    for (Team* t : g_live) {
        out_str_n(t->name.data(), (int)t->name.size());
        out_char(' ');
        out_int(rank++);
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
    rebuildDisplayedRank();
    printScoreboardFromLive();

    TeamCmp cmp;
    while (!g_frozen_teams.empty()) {
        auto it = std::prev(g_frozen_teams.end());
        Team* T = *it;
        int p = T->smallestFrozenProblem();
        bool gained_ac = (T->problems[p].first_ac_in_freeze != -1);

        Team* above = nullptr;
        if (gained_ac) {
            auto live_it = g_live.find(T);
            if (live_it != g_live.begin()) above = *std::prev(live_it);
            g_live.erase(live_it);
        }
        g_frozen_teams.erase(it);

        unfreezeProblemNoRankChange(T, p);

        if (gained_ac) {
            auto ins = g_live.insert(T).first;
            if (above != nullptr && cmp(T, above)) {
                auto next_it = std::next(ins);
                if (next_it != g_live.end()) {
                    Team* team2 = *next_it;
                    out_str_n(T->name.data(), (int)T->name.size());
                    out_char(' ');
                    out_str_n(team2->name.data(), (int)team2->name.size());
                    out_char(' ');
                    out_int(T->solved_count);
                    out_char(' ');
                    out_int(T->penalty);
                    out_char('\n');
                }
            }
        }
        if (T->frozen_problem_count > 0) g_frozen_teams.insert(T);
    }

    g_freeze_active = false;
    rebuildDisplayedRank();
    printScoreboardFromLive();
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
            p = readTok(p, probStr, sizeof(probStr));
            p = readTok(p, tmp, sizeof(tmp));
            p = readTok(p, teamName, sizeof(teamName));
            p = readTok(p, tmp, sizeof(tmp));
            p = readTok(p, statusStr, sizeof(statusStr));
            p = readTok(p, tmp, sizeof(tmp));
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
            p = readTok(p, tmp, sizeof(tmp));
            p = readUntilSpaceOrEq(p, tmp, sizeof(tmp));
            p = readKVValue(p, prob, sizeof(prob));
            p = readTok(p, tmp, sizeof(tmp));
            p = readUntilSpaceOrEq(p, tmp, sizeof(tmp));
            p = readKVValue(p, status, sizeof(status));
            querySubmission(name, prob, status);
        } else if (!strcmp(cmd, "START")) {
            char tmp[16];
            int d, pc;
            p = readTok(p, tmp, sizeof(tmp));
            p = readInt(p, &d);
            p = readTok(p, tmp, sizeof(tmp));
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
