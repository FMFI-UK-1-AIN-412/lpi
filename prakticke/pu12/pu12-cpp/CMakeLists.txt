cmake_minimum_required(VERSION 3.28)
project(Resolver)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")

add_executable(resolverTest
	Cnf.cpp
	Resolver.cpp
	ResolverTest.cpp
)

add_custom_target(run
    COMMAND resolverTest
    COMMENT "Running resolverTest"
)
