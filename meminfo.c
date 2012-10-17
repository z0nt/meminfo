/*_
 * Copyright (c) 2012 Andrey Zonov <zont@FreeBSD.org>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer,
 *    without modification, immediately at the beginning of the file.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <sys/param.h>

#include <sys/linker.h>
#include <sys/mman.h>
#define	_KERNEL
#include <sys/mount.h>
#undef _KERNEL
#include <sys/tree.h>
#include <sys/queue.h>
#define	_KVM_VNODE
#include <sys/vnode.h>

#include <ufs/ufs/quota.h>
#include <ufs/ufs/inode.h>

#include <vm/vm.h>
#include <vm/vm_object.h>
#include <vm/vm_page.h>
#include <vm/vm_param.h>

#include <err.h>
#include <fcntl.h>
#include <paths.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* from sys/kern/vfs_cache.c */
struct	namecache {
	LIST_ENTRY(namecache) nc_hash;	/* hash chain */
	LIST_ENTRY(namecache) nc_src;	/* source vnode list */
	TAILQ_ENTRY(namecache) nc_dst;	/* destination vnode list */
	struct	vnode *nc_dvp;		/* vnode of parent of name */
	struct	vnode *nc_vp;		/* vnode the name refers to */
	u_char	nc_flag;		/* flag bits */
	u_char	nc_nlen;		/* length of name */
	char	nc_name[0];		/* segment name + nul */
};

/*
 * Local vnode cache
 */
struct vncache {
	RB_ENTRY(vncache)  vlink;
	struct vnode	  *vp;
	u_long		   hits;
	char		  *fullpath;
};
static RB_HEAD(vnodes, vncache) vnodes = RB_INITIALIZER(&vnodes);
RB_PROTOTYPE_STATIC(vnodes, vncache, vlink, vnodecmp);

static int
vnodecmp(struct vncache *vc1, struct vncache *vc2)
{

	if (vc1->vp == vc2->vp)
		return (0);
	if (vc1->vp > vc2->vp)
		return (1);
	return (-1);
}
RB_GENERATE_STATIC(vnodes, vncache, vlink, vnodecmp);

static int fd;
static int mflag;
static char sym[] = "vm_page_queues";
static u_long objt_hits[OBJT_SG + 1];
static const char *objt_name[] = {
	"OBJT_DEFAULT",
	"OBJT_SWAP",
	"OBJT_VNODE",
	"OBJT_DEVICE",
	"OBJT_PHYS",
	"OBJT_DEAD",
	"OBJT_SG"
};

static void usage(void);
static void objt_report(void);
static void vn_report(void);
static void vn_acc(struct vnode *vp);
static struct vncache *vc_lookup(struct vnode *vp);
static struct vncache *vc_alloc(struct vnode *vp);
static void vc_insert(struct vncache *vc);
static void vn_fullpath(struct vnode *vp, char *buf);
static void vn_lookup(struct vnode *vp, char *buf, char **retbuf);

#define	MMAP(ptr, off)							\
	do {								\
		if ((off) == 0)						\
			errx(1, "zero offset at line: %d", __LINE__);	\
		(ptr) = mmap(0, sizeof(*(ptr)), PROT_READ,		\
		    MAP_SHARED, fd, (off_t)(off));			\
		if ((ptr) == MAP_FAILED)				\
			err(1, "mmap() failed at line: %d", __LINE__);	\
	} while (0)

#define MUNMAP(ptr)							\
	do {								\
		if (munmap((ptr), sizeof(*(ptr))) == -1)		\
			err(1, "munmap() failed at line: %d", __LINE__);\
	} while (0)

int
main(int argc, char **argv)
{
	int ch, objtreport, vnreport, queue;
	struct kld_sym_lookup kld;
	struct vpgqueues *page_queues;
	vm_page_t m, next;
	vm_object_t obj;

	objtreport = 0;
	vnreport = 0;
	queue = -1;
	while ((ch = getopt(argc, argv, "hmovq:")) != -1) {
		switch (ch) {
		case 'm':
			mflag = 1;
			break;
		case 'o':
			objtreport = 1;
			break;
		case 'v':
			vnreport = 1;
			break;
		case 'q':
			queue = strtol(optarg, NULL, 10);
			break;
		case 'h':
		default:
			usage();
		}
	}

	if (objtreport == 0 && vnreport == 0)
		usage();

	if (queue < PQ_INACTIVE || queue > PQ_HOLD)
		usage();

	fd = open(_PATH_KMEM, O_RDONLY, 0);
	if (fd == -1)
		err(1, "open(%s)", _PATH_KMEM);

	kld.version = sizeof(kld);
	kld.symname = sym;
	if (kldsym(0, KLDSYM_LOOKUP, &kld) == -1)
		err(1, "kldsym()");

	page_queues = mmap(0, sizeof(struct vpgqueues) * PQ_COUNT,
	    PROT_READ, MAP_SHARED, fd, kld.symvalue);
	if (page_queues == MAP_FAILED)
		err(1, "mmap()");

	for (m = TAILQ_FIRST(&page_queues[queue].pl); m != NULL; m = next) {
		MMAP(m, m);
		next = TAILQ_NEXT(m, pageq);
		if (m->object == 0) {
			MUNMAP(m);
			continue;
		}
		MMAP(obj, m->object);
		MUNMAP(m);

		switch (obj->type) {
		case OBJT_DEFAULT:
		case OBJT_SWAP:
			break;
		case OBJT_VNODE:
			if (vnreport)
				vn_acc(obj->handle);
			break;
		case OBJT_DEVICE:
		case OBJT_PHYS:
		case OBJT_DEAD:
		case OBJT_SG:
			break;
		default:
			errx(1, "Unknown object type: %d", obj->type);
		}
		objt_hits[obj->type]++;

		MUNMAP(obj);
	}

	if (objtreport)
		objt_report();

	if (vnreport)
		vn_report();

	exit(0);
}

static void
usage(void)
{

	fprintf(stderr, "usage: meminfo [-m] <-o|-v> -q queue\n"
			"  options:\n"
			"    -m report in megabytes\n"
			"    -o report about object types\n"
			"    -v report about vnode hits\n"
			"    -q page queue:\n"
			"       0 - PQ_INACTIVE\n"
			"       1 - PQ_ACTIVE\n"
			"       2 - PQ_HOLD\n");
	exit(1);
}

static void
objt_report(void)
{
	int i;
	u_long hits;

	for (i = OBJT_DEFAULT; i <= OBJT_SG; i++) {
		hits = objt_hits[i];
		if (mflag)
			hits = (hits * PAGE_SIZE) / 1024 / 1024;
		if (hits)
			printf("%12s = %lu\n", objt_name[i], hits);
	}
}

static void
vn_report(void)
{
	u_long hits;
	struct vncache *vc;

	RB_FOREACH(vc, vnodes, &vnodes) {
		hits = vc->hits;
		if (mflag)
			hits = (hits * PAGE_SIZE) / 1024 / 1024;
		if (hits)
			printf("%lu\t%s\n", hits, vc->fullpath);
	}
}

static void
vn_acc(struct vnode *vp)
{
	struct vncache *vc;

	/* Looking for a cached vnode */
	vc = vc_lookup(vp);
	if (vc == NULL) {
		/* Create new cached vnode */
		vc = vc_alloc(vp);
		/* Fill in path */
		vn_fullpath(vc->vp, vc->fullpath);
		/* Insert into tree */
		vc_insert(vc);
	}
	vc->hits++;
}

static struct vncache *
vc_lookup(struct vnode *vp)
{
	struct vncache key, *vc;

	key.vp = vp;
	vc = RB_FIND(vnodes, &vnodes, &key);

	return (vc);
}

static struct vncache *
vc_alloc(struct vnode *vp)
{
	struct vncache *vc;

	vc = malloc(sizeof(*vc));
	if (vc == NULL)
		err(1, "malloc(vc)");
	vc->vp = vp;
	vc->hits = 0;
	vc->fullpath = malloc(MAXPATHLEN);
	if (vc->fullpath == NULL)
		err(1, "malloc(fullpath)");
	vc->fullpath[0] = '\0';

	return (vc);
}

static void
vc_insert(struct vncache *vc)
{
	struct vncache *old;

	old = RB_INSERT(vnodes, &vnodes, vc);
	if (old != NULL)
		errx(1, "duplicate key");
}

static void
vn_fullpath(struct vnode *vp, char *buf)
{
	char *bufp;
	struct vnode *vmp;
	struct mount *mountp;

	bufp = buf;
	MMAP(vp, vp);
	MMAP(mountp, vp->v_mount);
	/* Mount point is not root */
	if (mountp->mnt_vnodecovered != NULL) {
		MMAP(vmp, mountp->mnt_vnodecovered);
		vn_lookup(vmp, buf, &bufp);
		MUNMAP(vmp);
	}
	MUNMAP(mountp);
	vn_lookup(vp, buf, &bufp);
	MUNMAP(vp);
}

static void
vn_lookup(struct vnode *vp, char *buf, char **retbuf)
{
	int len;
	struct inode *ip;
	struct vnode *dvp;
	struct namecache *ncp;

	ncp = TAILQ_FIRST(&vp->v_cache_dst);
	if (ncp != NULL) {
		MMAP(ncp, ncp);
		MMAP(dvp, ncp->nc_dvp);
		vn_lookup(dvp, buf, retbuf);
		MUNMAP(dvp);
		len = snprintf(*retbuf, ncp->nc_nlen + 2, "/%s", ncp->nc_name);
		*retbuf += len;
		MUNMAP(ncp);
	} else {
		if (vp->v_type == VREG) {
			MMAP(ip, vp->v_data);
			len = snprintf(*retbuf, MAXPATHLEN,
			    " inode=%d (deleted)", ip->i_number);
			*retbuf += len;
			MUNMAP(ip);
		}
	}
}
