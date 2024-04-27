from setuptools import find_packages, setup

setup(
    name='eznf',
    packages=find_packages(include=['eznf']),
    version='0.62.2',
    description='A library for easily encoding problems into SAT',
    author='Bernardo Subercaseaux',
    install_requires=[],
    setup_requires=['pytest-runner'],
    tests_require=['pytest'],
    test_suite='tests',
)
