#include "dlfcn.h"

#define INCL_BASE
#include <os2.h>
#include <float.h>

static ULONG retcode;
static char fail[300];

static ULONG dllHandle;
static char dllname[80];
static int handle_found;
static int handle_loaded;

#ifdef DLOPEN_INITTERM
unsigned long _DLL_InitTerm(unsigned long modHandle, unsigned long flag)
{
    switch (flag) {
    case 0:     /* INIT */
        /* Save handle */
        dllHandle = modHandle;
	handle_found = 1;
        return TRUE;

    case 1:     /* TERM */
	handle_found = 0;
        dllHandle = (unsigned long)NULLHANDLE;
        return TRUE;
    }

    return FALSE;
}

#endif

void *
dlopen(char *path, int mode)
{
	HMODULE handle;
	char tmp[260], *beg, *dot;
	ULONG rc;
	unsigned fpflag = _control87(0,0);

	fail[0] = 0;
	if (!path) {			/* Our own handle. */
	    if (handle_found) {
		if (handle_loaded)
		    return (void*)dllHandle;
		rc = DosQueryModuleName(dllHandle, sizeof(dllname), dllname);
		if (rc) {
	            strcpy(fail, "can't find my DLL name by the handle");
		    return 0;
		}
		rc = DosLoadModule(fail, sizeof fail, dllname, &handle);
		if (rc) {
	            strcpy(fail, "can't load my own DLL");
		    return 0;
		}
		handle_loaded = 1;
		goto ret;
	    }
            strcpy(fail, "can't load from myself: compiled without -DDLOPEN_INITTERM");
	    return 0;
	}
	if ((rc = DosLoadModule(fail, sizeof fail, path, &handle)) == 0)
		goto ret;

	retcode = rc;

	/* Not found. Check for non-FAT name and try truncated name. */
	/* Don't know if this helps though... */
	for (beg = dot = path + strlen(path);
	     beg > path && !strchr(":/\\", *(beg-1));
	     beg--)
		if (*beg == '.')
			dot = beg;
	if (dot - beg > 8) {
		int n = beg+8-path;
		memmove(tmp, path, n);
		memmove(tmp+n, dot, strlen(dot)+1);
		if (DosLoadModule(fail, sizeof fail, tmp, &handle) == 0)
			goto ret;
	}
	handle = 0;

      ret:
	_control87(fpflag, MCW_EM); /* Some modules reset FP flags on load */
	return (void *)handle;
}

void *
dlsym(void *handle, char *symbol)
{
	ULONG rc, type;
	PFN addr;

	fail[0] = 0;
	rc = DosQueryProcAddr((HMODULE)handle, 0, symbol, &addr);
	if (rc == 0) {
		rc = DosQueryProcType((HMODULE)handle, 0, symbol, &type);
		if (rc == 0 && type == PT_32BIT)
			return (void *)addr;
		rc = ERROR_CALL_NOT_IMPLEMENTED;
	}
	retcode = rc;
	return NULL;
}

char *
dlerror(void)
{
	static char buf[700];
	ULONG len;

	if (retcode == 0)
		return NULL;
	if (DosGetMessage(NULL, 0, buf, sizeof buf - 1, retcode,
			  "OSO001.MSG", &len)) {
		if (fail[0])
		  sprintf(buf, 
"OS/2 system error code %d, possible problematic module: '%s'",
			  (int)retcode, fail);
		else
		  sprintf(buf, "OS/2 system error code %d", (int)retcode);
	} else {
		buf[len] = '\0';
		if (len && buf[len - 1] == '\n')
			buf[--len] = 0;
		if (len && buf[len - 1] == '\r')
			buf[--len] = 0;
		if (len && buf[len - 1] == '.')
			buf[--len] = 0;
		if (fail[0] && len < 300)
		  sprintf(buf + len, ", possible problematic module: '%s'",
			  fail);
	}
	retcode = 0;
	return buf;
}

int
dlclose(void *handle)
{
	ULONG rc;

	if ((rc = DosFreeModule((HMODULE)handle)) == 0) return 0;

	retcode = rc;
	return 2;
}
