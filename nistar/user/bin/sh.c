/*
 * This is ported from xv6 shell, to make it compatible with POSIX,
 * plus line editing support via linenoise.
 */

#include <sys/wait.h>
#include <fcntl.h>
#include <linenoise.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <dirent.h>
#include <nistar/env.h>
#include <nistar/libfs.h>
#include <nistar/ulib.h>
#include <libgen.h>

/* Parsed command representation */
#define EXEC            1
#define REDIR           2
#define PIPE            3
#define LIST            4
#define BACK            5

#define MAXARGS         10

struct cmd {
        int type;
};

struct execcmd {
        int type;
        char *argv[MAXARGS];
        char *eargv[MAXARGS];
};

struct redircmd {
        int type;
        struct cmd *cmd;
        char *file;
        char *efile;
        int mode;
        int fd;
};

struct pipecmd {
        int type;
        struct cmd *left;
        struct cmd *right;
};

struct listcmd {
        int type;
        struct cmd *left;
        struct cmd *right;
};

struct backcmd {
        int type;
        struct cmd *cmd;
};

/* Fork but panics on failure. */
static int fork1(void);
struct cmd *parsecmd(char *);

/* Execute cmd.  Never returns. */
static _Noreturn void runcmd(struct cmd *cmd)
{
        int p[2];
        struct backcmd *bcmd;
        struct execcmd *ecmd;
        struct listcmd *lcmd;
        struct pipecmd *pcmd;
        struct redircmd *rcmd;

        if (cmd == 0)
                exit(0);

        switch (cmd->type) {
        default:
                panic("runcmd");

        case EXEC:
                ecmd = (struct execcmd *)cmd;
                if (ecmd->argv[0] == 0)
                        exit(0);
                execvp(ecmd->argv[0], ecmd->argv);
                fprintf(stderr, "exec %s failed\n", ecmd->argv[0]);
                break;

        case REDIR:
                rcmd = (struct redircmd *)cmd;
                close(rcmd->fd);
                if (open(rcmd->file, rcmd->mode) < 0) {
                        fprintf(stderr, "open %s failed\n", rcmd->file);
                        exit(0);
                }
                runcmd(rcmd->cmd);
                break;

        case LIST:
                lcmd = (struct listcmd *)cmd;
                if (fork1() == 0)
                        runcmd(lcmd->left);
                wait(NULL);
                runcmd(lcmd->right);
                break;

        case PIPE:
                pcmd = (struct pipecmd *)cmd;
                if (pipe(p) < 0)
                        panic("pipe");
                if (fork1() == 0) {
                        close(1);
                        dup(p[1]);
                        close(p[0]);
                        close(p[1]);
                        runcmd(pcmd->left);
                }
                if (fork1() == 0) {
                        close(0);
                        dup(p[0]);
                        close(p[0]);
                        close(p[1]);
                        runcmd(pcmd->right);
                }
                close(p[0]);
                close(p[1]);
                wait(NULL);
                wait(NULL);
                break;

        case BACK:
                bcmd = (struct backcmd *)cmd;
                if (fork1() == 0)
                        runcmd(bcmd->cmd);
                break;
        }

        exit(0);
}

static void emit_completion(const char *prefix, const char *dirname, const char *basename, linenoiseCompletions *lc)
{
        char emit[1024];
        DIR *dp;
        struct dirent *de;

        dp = opendir(dirname);
        if (dp == NULL)
                return;
        while ((de = readdir(dp)) != NULL) {
                if (strstr(de->d_name, basename) == de->d_name) {
                        strlcpy(emit, prefix, sizeof(emit));
                        strlcat(emit, de->d_name, sizeof(emit));
                        linenoiseAddCompletion(lc, emit);
                }
        }

        closedir(dp);
}

static void completion(const char *buf, linenoiseCompletions *lc) {
        return;
}

static char *hints(const char *buf, int *color, int *bold) {
    return NULL;
}

// Declassifier for stdo
static long stdio(dev_t dev, struct iobuf *io)
{
        switch (io->op) {
        case IO_OP_READ:
                return pread(0, io->buf, io->len, io->offset);
        case IO_OP_WRITE:
                return pwrite(1, io->buf, io->len, io->offset);
        }
}

int main(int argc, char **argv)
{
        char *buf;

        if (argc == 3 && !strcmp(argv[1], "-c"))
                runcmd(parsecmd(argv[2]));

        linenoiseSetCompletionCallback(completion);
        linenoiseSetHintsCallback(hints);

        // Create a declassifier for the current ownership set
        // for stdout / stderr / stdin

        // Anyone with the declassify tag can use the declassifier
        long r;
        usymlink_t gate;
        tag_t declassify = alloc_tag();
        struct label secrecy, integrity, ownership, guard;
        self_get_label(&secrecy, &integrity, &ownership);
        label_init(&guard);
        label_add_tag(&guard, declassify);

        r = alloc_call_gate(&gate, self_get_internal_container(), &secrecy, &integrity,
                            &ownership, &guard, self_get_pud(), stdio, 0, "declassifier");
        ASSERT_MSG(r == 0, "alloc_call_gate");

        // Wrap the declassify gate in an fd
        int dfd = hs_opengate(gate, O_RDWR);

        /* Read and run input commands. */
        while ((buf = linenoise("$ ")) != NULL) {
                /* Ignore empty lines. */
                if (!buf[0]) {
                        linenoiseFree(buf);
                        continue;
                }

                /* Add history. */
                linenoiseHistoryAdd(buf);

                if (buf[0] == 'c' && buf[1] == 'd' && buf[2] == ' ') {
                        /* Chdir must be called by the parent, not the child. */
                        if (chdir(buf + 3) < 0)
                                fprintf(stderr, "cannot cd %s\n", buf);
                        continue;
                }

                usymlink_t internal = self_get_internal_container();

                if (fork1() == 0) {
                        struct label secrecy, integrity, ownership;
                        self_get_label(&secrecy, &integrity, &ownership);
                        label_init(&ownership);
                        label_union(&ownership, &secrecy);
                        label_union(&ownership, &integrity);
                        // Give the child ownership of the declassifying tag
                        label_add_tag(&ownership, declassify);
                        self_set_label(&secrecy, &integrity, &ownership);

                        uint64_t qquota;

                        container_get_qquota(internal, &qquota);

                        // give some quota to the child
                        container_move_quota(internal, self_get_internal_container(), 128);
                        container_move_uquota(internal, self_get_internal_container(), 128);
                        container_move_qquota(internal, self_get_internal_container(), 5);
                        alloc_quanta(self_get_internal_container(), self_get(), 5);

                        // set up the declassifying fd as 0, 1 and 2
                        dup2(dfd, 0);
                        dup2(dfd, 1);
                        dup2(dfd, 2);
                        close(dfd);

                        runcmd(parsecmd(buf));
                }
                wait(NULL);
        }

        return 0;
}

static int fork1(void)
{
        int pid;

        pid = fork();
        if (pid == -1)
                panic("fork");
        return pid;
}

/* Constructors */

struct cmd *execcmd(void)
{
        struct execcmd *cmd;

        cmd = malloc(sizeof(*cmd));
        memset(cmd, 0, sizeof(*cmd));
        cmd->type = EXEC;
        return (struct cmd *)cmd;
}

struct cmd *redircmd(struct cmd *subcmd, char *file, char *efile, int mode,
                     int fd)
{
        struct redircmd *cmd;

        cmd = malloc(sizeof(*cmd));
        memset(cmd, 0, sizeof(*cmd));
        cmd->type = REDIR;
        cmd->cmd = subcmd;
        cmd->file = file;
        cmd->efile = efile;
        cmd->mode = mode;
        cmd->fd = fd;
        return (struct cmd *)cmd;
}

struct cmd *pipecmd(struct cmd *left, struct cmd *right)
{
        struct pipecmd *cmd;

        cmd = malloc(sizeof(*cmd));
        memset(cmd, 0, sizeof(*cmd));
        cmd->type = PIPE;
        cmd->left = left;
        cmd->right = right;
        return (struct cmd *)cmd;
}

struct cmd *listcmd(struct cmd *left, struct cmd *right)
{
        struct listcmd *cmd;

        cmd = malloc(sizeof(*cmd));
        memset(cmd, 0, sizeof(*cmd));
        cmd->type = LIST;
        cmd->left = left;
        cmd->right = right;
        return (struct cmd *)cmd;
}

struct cmd *backcmd(struct cmd *subcmd)
{
        struct backcmd *cmd;

        cmd = malloc(sizeof(*cmd));
        memset(cmd, 0, sizeof(*cmd));
        cmd->type = BACK;
        cmd->cmd = subcmd;
        return (struct cmd *)cmd;
}

/* Parsing */

static char whitespace[] = " \t\r\n\v";
static char symbols[] = "<|>&;()";

int gettoken(char **ps, char *es, char **q, char **eq)
{
        char *s;
        int ret;

        s = *ps;
        while (s < es && strchr(whitespace, *s))
                s++;
        if (q)
                *q = s;
        ret = *s;
        switch (*s) {
        case 0:
                break;
        case '|':
        case '(':
        case ')':
        case ';':
        case '&':
        case '<':
                s++;
                break;
        case '>':
                s++;
                if (*s == '>') {
                        ret = '+';
                        s++;
                }
                break;
        default:
                ret = 'a';
                while (s < es && !strchr(whitespace, *s) &&
                       !strchr(symbols, *s))
                        s++;
                break;
        }
        if (eq)
                *eq = s;

        while (s < es && strchr(whitespace, *s))
                s++;
        *ps = s;
        return ret;
}

int peek(char **ps, char *es, char *toks)
{
        char *s;

        s = *ps;
        while (s < es && strchr(whitespace, *s))
                s++;
        *ps = s;
        return *s && strchr(toks, *s);
}

struct cmd *parseline(char **, char *);
struct cmd *parsepipe(char **, char *);
struct cmd *parseexec(char **, char *);
struct cmd *nulterminate(struct cmd *);

struct cmd *parsecmd(char *s)
{
        char *es;
        struct cmd *cmd;

        es = s + strlen(s);
        cmd = parseline(&s, es);
        peek(&s, es, "");
        if (s != es) {
                fprintf(stderr, "leftovers: %s\n", s);
                panic("syntax");
        }
        nulterminate(cmd);
        return cmd;
}

struct cmd *parseline(char **ps, char *es)
{
        struct cmd *cmd;

        cmd = parsepipe(ps, es);
        while (peek(ps, es, "&")) {
                gettoken(ps, es, 0, 0);
                cmd = backcmd(cmd);
        }
        if (peek(ps, es, ";")) {
                gettoken(ps, es, 0, 0);
                cmd = listcmd(cmd, parseline(ps, es));
        }
        return cmd;
}

struct cmd *parsepipe(char **ps, char *es)
{
        struct cmd *cmd;

        cmd = parseexec(ps, es);
        if (peek(ps, es, "|")) {
                gettoken(ps, es, 0, 0);
                cmd = pipecmd(cmd, parsepipe(ps, es));
        }
        return cmd;
}

struct cmd *parseredirs(struct cmd *cmd, char **ps, char *es)
{
        int tok;
        char *q, *eq;

        while (peek(ps, es, "<>")) {
                tok = gettoken(ps, es, 0, 0);
                if (gettoken(ps, es, &q, &eq) != 'a')
                        panic("missing file for redirection");
                switch (tok) {
                case '<':
                        cmd = redircmd(cmd, q, eq, O_RDONLY, 0);
                        break;
                case '>':
                        cmd = redircmd(cmd, q, eq, O_WRONLY | O_CREAT, 1);
                        break;
                case '+': /* >> */
                        cmd = redircmd(cmd, q, eq, O_WRONLY | O_CREAT, 1);
                        break;
                }
        }
        return cmd;
}

struct cmd *parseblock(char **ps, char *es)
{
        struct cmd *cmd;

        if (!peek(ps, es, "("))
                panic("parseblock");
        gettoken(ps, es, 0, 0);
        cmd = parseline(ps, es);
        if (!peek(ps, es, ")"))
                panic("syntax - missing )");
        gettoken(ps, es, 0, 0);
        cmd = parseredirs(cmd, ps, es);
        return cmd;
}

struct cmd *parseexec(char **ps, char *es)
{
        char *q, *eq;
        int tok, argc;
        struct execcmd *cmd;
        struct cmd *ret;

        if (peek(ps, es, "("))
                return parseblock(ps, es);

        ret = execcmd();
        cmd = (struct execcmd *)ret;

        argc = 0;
        ret = parseredirs(ret, ps, es);
        while (!peek(ps, es, "|)&;")) {
                if ((tok = gettoken(ps, es, &q, &eq)) == 0)
                        break;
                if (tok != 'a')
                        panic("syntax");
                cmd->argv[argc] = q;
                cmd->eargv[argc] = eq;
                argc++;
                if (argc >= MAXARGS)
                        panic("too many args");
                ret = parseredirs(ret, ps, es);
        }
        cmd->argv[argc] = 0;
        cmd->eargv[argc] = 0;
        return ret;
}

/* NUL-terminate all the counted strings. */
struct cmd *nulterminate(struct cmd *cmd)
{
        int i;
        struct backcmd *bcmd;
        struct execcmd *ecmd;
        struct listcmd *lcmd;
        struct pipecmd *pcmd;
        struct redircmd *rcmd;

        if (cmd == 0)
                return 0;

        switch (cmd->type) {
        case EXEC:
                ecmd = (struct execcmd *)cmd;
                for (i = 0; ecmd->argv[i]; i++)
                        *ecmd->eargv[i] = 0;
                break;

        case REDIR:
                rcmd = (struct redircmd *)cmd;
                nulterminate(rcmd->cmd);
                *rcmd->efile = 0;
                break;

        case PIPE:
                pcmd = (struct pipecmd *)cmd;
                nulterminate(pcmd->left);
                nulterminate(pcmd->right);
                break;

        case LIST:
                lcmd = (struct listcmd *)cmd;
                nulterminate(lcmd->left);
                nulterminate(lcmd->right);
                break;

        case BACK:
                bcmd = (struct backcmd *)cmd;
                nulterminate(bcmd->cmd);
                break;
        }
        return cmd;
}
