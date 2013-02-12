/*-
 * Copyright (c) 2012, 2013 Andrey Zonov <zont@FreeBSD.org>
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

#include <sys/conf.h>
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
 * Local vm objects cache
 */
struct objcache {
	RB_ENTRY(objcache)	 olink;
	vm_object_t		 obj;
	objtype_t		 type;
	struct vnode		*vp;
};

static RB_HEAD(objects, objcache) objects = RB_INITIALIZER(&objects);
RB_PROTOTYPE_STATIC(objects, objcache, olink, objcmp);

static int
objcmp(struct objcache *objc1, struct objcache *objc2)
{

	if (objc1->obj == objc2->obj)
		return (0);
	if (objc1->obj > objc2->obj)
		return (1);
	return (-1);
}
RB_GENERATE_STATIC(objects, objcache, olink, objcmp);

/*
 * Local vnodes cache
 */
struct vncache {
	RB_ENTRY(vncache)	 vlink;
	struct vnode		*vp;
	u_long			 hits;
	char			*fullpath;
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

static char vm_page_array_sym[] = "vm_page_array";
static char vm_page_array_size_sym[] = "vm_page_array_size";
static int fd;
static int mflag;
static int actreport;
static int objtreport;
static int vnreport;
static u_long act_counts[ACT_MAX + 1];
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
static void obj_acc(vm_object_t obj);
static void obj_handle(vm_object_t obj, struct objcache *objc);
static struct objcache *obj_lookup(vm_object_t obj);
static struct objcache *obj_alloc(vm_object_t obj);
static void obj_insert(struct objcache *objc);

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
	int ch, queue;
	long i, *data;
	off_t vm_page_array_off, vm_page_array_size;
	struct kld_sym_lookup kld;
	vm_page_t m, vm_page_array = NULL;

	queue = -1;
	while ((ch = getopt(argc, argv, "ahmovq:")) != -1) {
		switch (ch) {
		case 'a':
			actreport = 1;
			break;
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

	if (actreport == 0 && objtreport == 0 && vnreport == 0)
		usage();

	if (queue < PQ_INACTIVE || queue > PQ_ACTIVE)
		usage();

	if (actreport && queue != PQ_ACTIVE) {
		fprintf(stderr, "Maybe used only for active queue\n");
		exit(1);
	}

	fd = open(_PATH_KMEM, O_RDONLY, 0);
	if (fd == -1)
		err(1, "open(%s)", _PATH_KMEM);

	kld.version = sizeof(kld);
	kld.symname = vm_page_array_sym;
	if (kldsym(0, KLDSYM_LOOKUP, &kld) == -1)
		err(1, "kldsym()");
	MMAP(data, kld.symvalue);
	vm_page_array_off = *data;
	MUNMAP(data);

	kld.version = sizeof(kld);
	kld.symname = vm_page_array_size_sym;
	if (kldsym(0, KLDSYM_LOOKUP, &kld) == -1)
		err(1, "kldsym()");
	MMAP(data, kld.symvalue);
	vm_page_array_size = *data;
	MUNMAP(data);

#define	REMAP	(10000)
	for (i = 0; i < vm_page_array_size; i++) {
		if (i % REMAP == 0) {
			if (i > 0)
				if (munmap(vm_page_array,
				    sizeof(struct vm_page) * REMAP) == -1)
					err(1, "munmap()");
			vm_page_array = mmap(0, sizeof(struct vm_page) * REMAP,
			    PROT_READ, MAP_SHARED, fd,
			    vm_page_array_off + sizeof(struct vm_page) * i);
			if (vm_page_array == MAP_FAILED)
				err(1, "mmap()");
		}
		m = &vm_page_array[i % REMAP];
		if (m->queue != queue)
			continue;
		if (actreport)
			act_counts[m->act_count]++;
		if (m->object != NULL)
			obj_acc(m->object);
	}

	if (actreport) {
		for (i = 0; i <= ACT_MAX; i++) {
			if (act_counts[i] > 0)
				printf("act[%ld] = %lu\n", i, act_counts[i]);
		}
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

	fprintf(stderr, "usage: meminfo [-m] <-a|-o|-v> -q queue\n"
			"  options:\n"
			"    -a report about active counts\n"
			"    -m report in megabytes\n"
			"    -o report about object types\n"
			"    -v report about vnode hits\n"
			"    -q page queue:\n"
			"       0 - PQ_INACTIVE\n"
			"       1 - PQ_ACTIVE\n");
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
obj_acc(vm_object_t obj)
{
	struct objcache *objc;

	/* Looking for a cached object */
	objc = obj_lookup(obj);
	if (objc == NULL) {
		/* Create new cached object */
		objc = obj_alloc(obj);
		/* Handle it */
		obj_handle(obj, objc);
		/* Insert it into tree */
		obj_insert(objc);
	}

	if (objtreport)
		objt_hits[objc->type]++;
	if (vnreport) {
		if (objc->type == OBJT_VNODE)
			vn_acc(objc->vp);
	}
}

static void
obj_handle(vm_object_t obj, struct objcache *objc)
{

	MMAP(obj, obj);

	switch (obj->type) {
	case OBJT_DEFAULT:
	case OBJT_SWAP:
		break;
	case OBJT_VNODE:
		objc->vp = obj->handle;
		break;
	case OBJT_DEVICE:
	case OBJT_PHYS:
	case OBJT_DEAD:
	case OBJT_SG:
		break;
	default:
		errx(1, "Unknown object type: %d", obj->type);
	}
	objc->type = obj->type;

	MUNMAP(obj);
}

static struct objcache *
obj_lookup(vm_object_t obj)
{
	struct objcache key, *objc;

	key.obj = obj;
	objc = RB_FIND(objects, &objects, &key);

	return (objc);
}

static struct objcache *
obj_alloc(vm_object_t obj)
{
	struct objcache *objc;

	objc = malloc(sizeof(*objc));
	if (objc == NULL)
		err(1, "malloc(objc)");
	objc->obj = obj;

	return (objc);
}

static void
obj_insert(struct objcache *objc)
{
	struct objcache *old;

	old = RB_INSERT(objects, &objects, objc);
	if (old != NULL)
		errx(1, "duplicate vm object key");
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
		errx(1, "duplicate vnode key");
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
	struct cdev *dev;
	struct inode *ip;
	struct vnode *dvp;
	struct namecache *ncp;

	if (vp->v_vflag & VV_ROOT)
		return;

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
		if (vp->v_type == VREG || vp->v_type == VDIR) {
			MMAP(ip, vp->v_data);
			len = snprintf(*retbuf, MAXPATHLEN - (*retbuf - buf),
			    "/(%s inode=%d)",
			    ip->i_nlink ? "no cached name for" : "deleted",
			    ip->i_number);
			*retbuf += len;
			MUNMAP(ip);
		} else if (vp->v_type == VCHR) {
			MMAP(dev, vp->v_un.vu_cdev);
			len = snprintf(*retbuf, MAXPATHLEN - (*retbuf - buf),
			    "/%s (cdev)", /* dev->si_name */
			    (char *)dev + sizeof(*dev) - (SPECNAMELEN + 1));
			*retbuf += len;
			MUNMAP(dev);
		} else
			errx(1, "Unknown vnode type: %d", vp->v_type);
	}
}
