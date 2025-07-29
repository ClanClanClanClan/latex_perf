from setuptools import setup, find_packages

setup(
    name="latex-perfectionist",
    version="24.0.0",
    description="Formally verified LaTeX validation with 542+ rules",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    author="LaTeX Perfectionist Team",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    python_requires=">=3.8",
    install_requires=[
        "pyyaml>=6.0",
        "click>=8.0",
        "rich>=10.0",
    ],
    extras_require={
        "dev": [
            "pytest>=7.0",
            "pytest-cov>=4.0",
            "black>=22.0",
            "isort>=5.0",
            "flake8>=5.0",
            "mypy>=1.0",
        ]
    },
    entry_points={
        "console_scripts": [
            "latex-perfectionist=latex_perfectionist.cli.main:cli",
        ]
    },
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
    ],
)