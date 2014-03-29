/*
 * mytop.cpp
 *
 *  Created on: Mar 29, 2014
 *      Author: guang
 */

#include "mytop.h"
#include <stdio.h>
#include <string>
#include <cstdarg>

//utitlity function for std::string format
std::string string_format(const std::string fmt, ...) {
    int size = 100;
    std::string str;
    va_list ap;
    while (1) {
        str.resize(size);
        va_start(ap, fmt);
        int n = vsnprintf((char *)str.c_str(), size, fmt.c_str(), ap);
        va_end(ap);
        if (n > -1 && n < size) {
            str.resize(n);
            return str;
        }
        if (n > -1)
            size = n + 1;
        else
            size *= 2;
    }
    return str;
}

#include <ctype.h>
#include <dirent.h>
#include <grp.h>
#include <pwd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

struct cpu_info {
    long unsigned utime, ntime, stime, itime;
};

struct proc_info {
    struct proc_info *next;
    pid_t pid;
    pid_t tid;
    uid_t uid;
    gid_t gid;
    char name[256];
    char state;
    long unsigned utime;
    long unsigned stime;
    long unsigned delta_utime;
    long unsigned delta_stime;
    long unsigned delta_time;
    long vss;
    long rss;
    int num_threads;
};

struct proc_list {
    struct proc_info **array;
    int size;
};

#define die(...) { fprintf(stderr, __VA_ARGS__); exit(EXIT_FAILURE); }

#define INIT_PROCS 50
#define THREAD_MULT 4
static struct proc_info **old_procs, **new_procs;
static int num_old_procs, num_new_procs;
static struct proc_info *free_procs;
static int num_used_procs, num_free_procs;

static int max_procs, threads;

static struct cpu_info old_cpu, new_cpu;

static struct proc_info *alloc_proc(void);
static void free_proc(struct proc_info *proc);
static void read_procs(void);
static int read_stat(char *filename, struct proc_info *proc);
static void add_proc(int proc_num, struct proc_info *proc);
static int read_cmdline(char *filename, struct proc_info *proc);
static int read_status(char *filename, struct proc_info *proc);
std::string print_procs(void);
static struct proc_info *find_old_proc(pid_t pid, pid_t tid);
static void free_old_procs(void);
static int (*proc_cmp)(const void *a, const void *b);
static int proc_cpu_cmp(const void *a, const void *b);
static int numcmp(long long a, long long b);

static struct proc_info *alloc_proc(void) {
    struct proc_info *proc;

    if (free_procs) {
        proc = free_procs;
        free_procs = free_procs->next;
        num_free_procs--;
    } else {
        proc = (proc_info*)malloc(sizeof(*proc));
        if (!proc) die("Could not allocate struct process_info.\n");
    }

    num_used_procs++;

    return proc;
}

static void free_proc(struct proc_info *proc) {
    proc->next = free_procs;
    free_procs = proc;

    num_used_procs--;
    num_free_procs++;
}

#define MAX_LINE 256

static void read_procs(void) {
    DIR *proc_dir, *task_dir;
    struct dirent *pid_dir, *tid_dir;
    char filename[64];
    FILE *file;
    int proc_num;
    struct proc_info *proc;
    pid_t pid, tid;

    int i;

    proc_dir = opendir("/proc");
    if (!proc_dir) die("Could not open /proc.\n");

    new_procs = (proc_info**)calloc(INIT_PROCS * (threads ? THREAD_MULT : 1), sizeof(struct proc_info *));
    num_new_procs = INIT_PROCS * (threads ? THREAD_MULT : 1);

    file = fopen("/proc/stat", "r");
    if (!file) die("Could not open /proc/stat.\n");
    fscanf(file, "cpu  %lu %lu %lu %lu", &new_cpu.utime, &new_cpu.ntime, &new_cpu.stime, &new_cpu.itime);
    fclose(file);

    proc_num = 0;
    while ((pid_dir = readdir(proc_dir))) {
        if (!isdigit(pid_dir->d_name[0]))
            continue;

        pid = atoi(pid_dir->d_name);

        if (!threads) {
            proc = alloc_proc();

            proc->pid = proc->tid = pid;

            sprintf(filename, "/proc/%d/stat", pid);
            read_stat(filename, proc);

            sprintf(filename, "/proc/%d/cmdline", pid);
            read_cmdline(filename, proc);

            sprintf(filename, "/proc/%d/status", pid);
            read_status(filename, proc);

            proc->num_threads = 0;
        } else {
            proc = NULL;
        }

        sprintf(filename, "/proc/%d/task", pid);
        task_dir = opendir(filename);
        if (!task_dir) continue;

        while ((tid_dir = readdir(task_dir))) {
            if (!isdigit(tid_dir->d_name[0]))
                continue;

            if (threads) {
                tid = atoi(tid_dir->d_name);

                proc = alloc_proc();

                proc->pid = pid; proc->tid = tid;

                sprintf(filename, "/proc/%d/task/%d/stat", pid, tid);
                read_stat(filename, proc);

                sprintf(filename, "/proc/%d/task/%d/cmdline", pid, tid);
                read_cmdline(filename, proc);

                sprintf(filename, "/proc/%d/task/%d/status", pid, tid);
                read_status(filename, proc);

                add_proc(proc_num++, proc);
            } else {
                proc->num_threads++;
            }
        }

        closedir(task_dir);
        
        if (!threads)
            add_proc(proc_num++, proc);
    }

    for (i = proc_num; i < num_new_procs; i++)
        new_procs[i] = NULL;

    closedir(proc_dir);
}

static int read_stat(char *filename, struct proc_info *proc) {
    FILE *file;
    char buf[MAX_LINE], *open_paren, *close_paren;

    file = fopen(filename, "r");
    if (!file) return 1;
    fgets(buf, MAX_LINE, file);
    fclose(file);

    /* Split at first '(' and last ')' to get process name. */
    open_paren = strchr(buf, '(');
    close_paren = strrchr(buf, ')');
    if (!open_paren || !close_paren) return 1;

    *open_paren = *close_paren = '\0';
    strcpy(proc->name, open_paren + 1);

    /* Scan rest of string. */
    sscanf(close_paren + 1, " %c %*d %*d %*d %*d %*d %*d %*d %*d %*d %*d "
                 "%lu %lu %*d %*d %*d %*d %*d %*d %*d %lu %ld",
                 &proc->state, &proc->utime, &proc->stime, &proc->vss, &proc->rss);

    return 0;
}

static void add_proc(int proc_num, struct proc_info *proc) {
    int i;

    if (proc_num >= num_new_procs) {
        new_procs = (proc_info**)realloc(new_procs, 2 * num_new_procs * sizeof(struct proc_info *));
        if (!new_procs) die("Could not expand procs array.\n");
        for (i = num_new_procs; i < 2 * num_new_procs; i++)
            new_procs[i] = NULL;
        num_new_procs = 2 * num_new_procs;
    }
    new_procs[proc_num] = proc;
}

static int read_cmdline(char *filename, struct proc_info *proc) {
    FILE *file;
    char line[MAX_LINE];

    line[0] = '\0';
    file = fopen(filename, "r");
    if (!file) return 1;
    fgets(line, MAX_LINE, file);
    fclose(file);
    if (strlen(line) > 0)
        strcpy(proc->name, line);
    return 0;
}

static int read_status(char *filename, struct proc_info *proc) {
    FILE *file;
    char line[MAX_LINE];
    unsigned int uid, gid;

    file = fopen(filename, "r");
    if (!file) return 1;
    while (fgets(line, MAX_LINE, file)) {
        sscanf(line, "Uid: %u", &uid);
        sscanf(line, "Gid: %u", &gid);
    }
    fclose(file);
    proc->uid = uid; proc->gid = gid;
    return 0;
}

std::string print_procs(void) {
    int i;
    struct proc_info *old_proc, *proc;
    long unsigned total_delta_time;
    struct passwd *user;
    struct group *group;
    char *user_str, user_buf[20];
    char *group_str, group_buf[20];

    for (i = 0; i < num_new_procs; i++) {
        if (new_procs[i]) {
            old_proc = find_old_proc(new_procs[i]->pid, new_procs[i]->tid);
            if (old_proc) {
                new_procs[i]->delta_utime = new_procs[i]->utime - old_proc->utime;
                new_procs[i]->delta_stime = new_procs[i]->stime - old_proc->stime;
            } else {
                new_procs[i]->delta_utime = 0;
                new_procs[i]->delta_stime = 0;
            }
            new_procs[i]->delta_time = new_procs[i]->delta_utime + new_procs[i]->delta_stime;
        }
    }

    total_delta_time = (new_cpu.utime + new_cpu.ntime + new_cpu.stime + new_cpu.itime)
                     - (old_cpu.utime + old_cpu.ntime + old_cpu.stime + old_cpu.itime);

    qsort(new_procs, num_new_procs, sizeof(struct proc_info *), proc_cmp);

    std::string output("\n\n\n");
    
    if (!threads)
    {
    	  output += string_format("%5s %4s %1s %5s %7s %7s %-8s %s\n", "PID", "CPU%", "S", "#THR", "VSS", "RSS", "UID", "Name");
    }
    else
    {
        output += string_format("%5s %5s %4s %1s %7s %7s %-8s %s\n", "PID", "TID", "CPU%", "S", "VSS", "RSS", "UID", "Name");
    }

    for (i = 0; i < num_new_procs; i++) {
        proc = new_procs[i];

        if (!proc || (max_procs && (i >= max_procs)))
            break;
        user  = getpwuid(proc->uid);
        group = getgrgid(proc->gid);
        if (user && user->pw_name) {
            user_str = user->pw_name;
        } else {
            snprintf(user_buf, 20, "%d", proc->uid);
            user_str = user_buf;
        }
        if (group && group->gr_name) {
            group_str = group->gr_name;
        } else {
            snprintf(group_buf, 20, "%d", proc->gid);
            group_str = group_buf;
        }
        if (!threads) 
            output += string_format("%5d %3ld%% %c %5d %6ldK %6ldK %-8.8s %s\n", proc->pid, proc->delta_time * 100 / total_delta_time, proc->state, proc->num_threads,
                proc->vss / 1024, proc->rss * getpagesize() / 1024, user_str, proc->name);
        else
            output += string_format("%5d %5d %3ld%% %c %6ldK %6ldK %-8.8s %s\n", proc->pid, proc->tid, proc->delta_time * 100 / total_delta_time, proc->state,
                proc->vss / 1024, proc->rss * getpagesize() / 1024, user_str, proc->name);
    }
    return output;
}

static struct proc_info *find_old_proc(pid_t pid, pid_t tid) {
    int i;

    for (i = 0; i < num_old_procs; i++)
        if (old_procs[i] && (old_procs[i]->pid == pid) && (old_procs[i]->tid == tid))
            return old_procs[i];

    return NULL;
}

static void free_old_procs(void) {
    int i;

    for (i = 0; i < num_old_procs; i++)
        if (old_procs[i])
            free_proc(old_procs[i]);

    free(old_procs);
}

static int proc_cpu_cmp(const void *a, const void *b) {
    struct proc_info *pa, *pb;

    pa = *((struct proc_info **)a); pb = *((struct proc_info **)b);

    if (!pa && !pb) return 0;
    if (!pa) return 1;
    if (!pb) return -1;

    return -numcmp(pa->delta_time, pb->delta_time);
}

static int numcmp(long long a, long long b) {
    if (a < b) return -1;
    if (a > b) return 1;
    return 0;
}

mytop::mytop() {	
}

mytop::~mytop() {	
}

std::string mytop::top() 
{
    num_used_procs = num_free_procs = 0;
    max_procs = 0;
    proc_cmp = &proc_cpu_cmp;
	num_new_procs = num_old_procs = 0;
    new_procs = old_procs = NULL;
    read_procs();
	old_procs = new_procs;
	num_old_procs = num_new_procs;
	memcpy(&old_cpu, &new_cpu, sizeof(old_cpu));
	read_procs();
	std::string get_top = print_procs();
	free_old_procs();
	return get_top;	
}
