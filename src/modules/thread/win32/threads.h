/**
* Copyright (c) 2006-2011 LOVE Development Team
*
* This software is provided 'as-is', without any express or implied
* warranty.  In no event will the authors be held liable for any damages
* arising from the use of this software.
*
* Permission is granted to anyone to use this software for any purpose,
* including commercial applications, and to alter it and redistribute it
* freely, subject to the following restrictions:
*
* 1. The origin of this software must not be misrepresented; you must not
*    claim that you wrote the original software. If you use this software
*    in a product, an acknowledgment in the product documentation would be
*    appreciated but is not required.
* 2. Altered source versions must be plainly marked as such, and must not be
*    misrepresented as being the original software.
* 3. This notice may not be removed or altered from any source distribution.
**/

#ifndef LOVE_THREAD_WIN32_THREADS_H
#define LOVE_THREAD_WIN32_THREADS_H

#include <windows.h>
#include <limits.h>

namespace love
{
namespace thread
{

	class Mutex
	{
	private:
		CRITICAL_SECTION mutex;
		Mutex(const Mutex& mutex) {}

	public:
		Mutex();
		~Mutex();

		 void lock();
		 void unlock();
	};

	class ThreadBase
	{
	private:
		HANDLE thread;
		ThreadBase(ThreadBase& thread) {}
		bool running;

		static int WINAPI thread_runner(void* param);

	protected:

		virtual void main() = 0;

	public:
		ThreadBase();
		virtual ~ThreadBase();

		bool start();
		void wait();
		void kill();

		static unsigned int threadId();
	};


	class Semaphore
	{
	private:
		Semaphore(const Semaphore& sem) {}
		HANDLE semaphore;
		unsigned int count;

	public:
		Semaphore(unsigned int initial_value = 0);
		~Semaphore();

		unsigned int value();
		void post();
		bool wait(int timeout = -1);
		bool tryWait();
	};


	// Should conditional inherit from mutex?
	class Conditional
	{
	private:
		Mutex mutex;
		int waiting;
		int signals;
		Semaphore sem;
		Semaphore done;

	public:
		Conditional();
		~Conditional();

		void signal();
		void broadcast();
		bool wait(Mutex* cmutex, int timeout=-1);
	};
} // thread
} // love

#endif /* LOVE_THREAD_WIN32_THREADS_H */
