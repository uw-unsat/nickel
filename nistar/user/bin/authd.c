#include <nistar/env.h>
#include <nistar/libfs.h>
#include <nistar/ulib.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>


#define USERNAME_MAXLEN 512
#define PASSWORD_MAXLEN 512
#define NUSERS 10

struct user {
        char username[USERNAME_MAXLEN];
        char password[PASSWORD_MAXLEN];
        struct label secrecy;
        struct label integrity;
        struct label ownership;
};

static struct user users[NUSERS];

static struct user createuser(char username[USERNAME_MAXLEN], char password[PASSWORD_MAXLEN])
{
        struct user u;
        tag_t user_secrecy = alloc_tag();
        tag_t user_integrity = alloc_tag();

        struct label secrecy, integrity, ownership;
        label_init(&secrecy);
        label_init(&integrity);
        label_init(&ownership);

        label_add_tag(&secrecy, user_secrecy);
        label_add_tag(&integrity, user_integrity);
        label_add_tag(&ownership, user_secrecy);
        label_add_tag(&ownership, user_integrity);

        strlcpy(u.username, username, sizeof(u.username));
        strlcpy(u.password, password, sizeof(u.password));

        u.secrecy = secrecy;
        u.integrity = integrity;
        u.ownership = ownership;

        char homepath[128];
        strlcpy(homepath, "/home/", sizeof(homepath));
        strlcat(homepath, username, sizeof(homepath));

        self_get_label(&secrecy, &integrity, NULL);

        // Create a homedir for the new user with user's labels
        self_set_label(&u.secrecy, &u.integrity, NULL);

        hs_mkdir(homepath, 0);

        // Restore authd labels
        self_set_label(&secrecy, &integrity, NULL);

        return u;
}

static void _init_users()
{
        users[0] = createuser("a", "a");
        users[1] = createuser("b", "b");
}

int main(int argv, char **argc)
{
        struct label auth_secrecy, auth_integrity, auth_ownership;
        self_get_label(&auth_secrecy, &auth_integrity, &auth_ownership);

        _init_users();

        usymlink_t icont = self_get_internal_container();

        // log in the next user
        int i = 0;

        struct user *u = &users[i];


        while (1) {
                struct label secrecy, integrity, ownership;
                self_get_label(&secrecy, &integrity, &ownership);

                // Set the secrecy and integrity labels to the user's before
                // fork (so the fork'd space is only tainted by those)
                label_copy(&secrecy, &u->secrecy);
                label_copy(&integrity, &u->integrity);
                self_set_label(&secrecy, &integrity, &ownership);

                if (fork() == 0) {
                        uint64_t qquota;
                        container_get_qquota(icont, &qquota);

                        // allocate quota for the user
                        container_move_quota(icont, self_get_internal_container(), 1024);
                        container_move_uquota(icont, self_get_internal_container(), 400);
                        // Give all but one quantum to child (init retains one)
                        container_move_qquota(icont, self_get_internal_container(), qquota - 1);
                        alloc_quanta(self_get_internal_container(), self_get(), qquota - 1);

                        // Give the user its ownerhip labels
                        debug_print_label(&secrecy);
                        debug_print_label(&integrity);
                        debug_print_label(&u->ownership);

                        // Spawn the shell using the user's ownership labels
                        label_copy(&ownership, &u->ownership);
                        self_set_label(&secrecy, &integrity, &ownership);

                        setenv("PATH", "/bin/", 0);
                        execl("/bin/sh", "/bin/sh", NULL);
                        exit(0);
                }

                wait(NULL);

                i = (i + 1) % 2;

                u = &users[i];
        }
        return 0;
}
