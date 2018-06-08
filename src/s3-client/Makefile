
ifdef VERBOSE
        VERBOSE = true
        VERBOSE_ECHO = @ echo
        VERBOSE_SHOW =
        QUIET_ECHO = @ echo > /dev/null
else
        VERBOSE = false
        VERBOSE_ECHO = @ echo > /dev/null
        VERBOSE_SHOW = @
        QUIET_ECHO = @ echo
endif


# --------------------------------------------------------------------------
# BUILD directory
ifndef BUILD
    ifdef DEBUG
        BUILD := build-debug
    else
        BUILD := build
    endif
endif


# --------------------------------------------------------------------------
# DESTDIR directory
ifndef DESTDIR
    DESTDIR := /usr
endif


# --------------------------------------------------------------------------
# Acquire configuration information for libraries that libs3 depends upon

ifndef CURL_LIBS
    CURL_LIBS := $(shell curl-config --libs)
endif

ifndef CURL_CFLAGS
    CURL_CFLAGS := $(shell curl-config --cflags)
endif

ifndef LIBXML2_LIBS
    LIBXML2_LIBS := $(shell xml2-config --libs)
endif

ifndef LIBXML2_CFLAGS
    LIBXML2_CFLAGS := $(shell xml2-config --cflags)
endif


# --------------------------------------------------------------------------
# These CFLAGS assume a GNU compiler.  For other compilers, write a script
# which converts these arguments into their equivalent for that particular
# compiler.

ifndef CFLAGS
    ifdef DEBUG
        CFLAGS := -g
    else
        CFLAGS := -O3
    endif
endif

CFLAGS += -Wall -Werror -Wshadow -Wextra -Iinclude \
          $(CURL_CFLAGS) $(LIBXML2_CFLAGS) \
          -DLIBS3_VER_MAJOR=\"$(LIBS3_VER_MAJOR)\" \
          -DLIBS3_VER_MINOR=\"$(LIBS3_VER_MINOR)\" \
          -DLIBS3_VER=\"$(LIBS3_VER)\" \
          -D__STRICT_ANSI__ \
          -D_ISOC99_SOURCE \
          -D_POSIX_C_SOURCE=200112L

LDFLAGS = $(CURL_LIBS) $(LIBXML2_LIBS) -lpthread

LIBRARY = ../lib/libs3.a 

# --------------------------------------------------------------------------
# Default targets are everything

.PHONY: all
all: s3

# --------------------------------------------------------------------------
# Compile target patterns

$(BUILD)/obj/%.o: src/%.c
	$(QUIET_ECHO) $@: Compiling object
	@ mkdir -p $(dir $(BUILD)/dep/$<)
	@ gcc $(CFLAGS) -M -MG -MQ $@ -DCOMPILINGDEPENDENCIES \
        -o $(BUILD)/dep/$(<:%.c=%.d) -c $<
	@ mkdir -p $(dir $@)
	$(VERBOSE_SHOW) gcc $(CFLAGS) -o $@ -c $<


# --------------------------------------------------------------------------
# Driver program targets

.PHONY: s3
s3: $(BUILD)/bin/s3

$(BUILD)/bin/s3: $(BUILD)/obj/s3.o
	$(QUIET_ECHO) $@: Building executable
	@ mkdir -p $(dir $@)
	$(VERBOSE_SHOW) gcc -o $@ $^ $(LDFLAGS) $(LIBRARY)

# --------------------------------------------------------------------------
# Clean target

.PHONY: clean
clean:
	$(QUIET_ECHO) $(BUILD): Cleaning
	$(VERBOSE_SHOW) rm -rf $(BUILD)
